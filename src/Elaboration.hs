{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language ScopedTypeVariables #-}
{-# language ViewPatterns #-}
module Elaboration where

import Protolude hiding (Seq, force, check, evaluate, until)

import Data.IORef
import Rock
import qualified Data.HashSet as HashSet

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Elaboration.Metas as Metas
import Error (Error)
import qualified Error
import qualified Evaluation
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import qualified Presyntax
import qualified "this" Data.IntMap as IntMap
import Plicity
import qualified Query
import qualified Readback
import qualified Scope
import qualified Syntax
import Telescope (Telescope)
import qualified Telescope
import qualified Unification

newtype InstantiateUntil = InstantiateUntil Plicity

---------------------------------------------------------------------------------

inferTopLevelDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> M ((Syntax.Definition, Syntax.Type Void), [Error])
inferTopLevelDefinition key def = do
  context <- Context.empty key
  (def', typeValue) <- inferDefinition context def
  type_ <- readback context typeValue
  metas <- checkMetaSolutions context
  result <- Metas.inlineSolutions metas def' type_
  errors <- liftIO $ readIORef (Context.errors context)
  pure (result, toList errors)

checkTopLevelDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> Domain.Type
  -> M (Syntax.Definition, [Error])
checkTopLevelDefinition key def type_ = do
  context <- Context.empty key
  def' <- checkDefinition context def type_
  metas <- checkMetaSolutions context
  (def'', _) <- Metas.inlineSolutions metas def' $ Syntax.Global Builtin.fail
  errors <- liftIO $ readIORef $ Context.errors context
  pure (def'', toList errors)

checkDefinition
  :: Context Void
  -> Presyntax.Definition
  -> Domain.Type
  -> M Syntax.Definition
checkDefinition context def expectedType =
  case def of
    Presyntax.TypeDeclaration type_ -> do
      type' <- check context type_ expectedType
      pure $ Syntax.TypeDeclaration type'

    Presyntax.ConstantDefinition term -> do
      term' <- check context term expectedType
      pure $ Syntax.ConstantDefinition term'

    Presyntax.DataDefinition params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs
      type' <- evaluate context type_
      Unification.unify context type' expectedType
      pure $ Syntax.DataDefinition tele

inferDefinition
  :: Context Void
  -> Presyntax.Definition
  -> M (Syntax.Definition, Domain.Type)
inferDefinition context def =
  case def of
    Presyntax.TypeDeclaration type_ -> do
      type' <- check context type_ Builtin.type_
      pure (Syntax.TypeDeclaration type', Builtin.type_)

    Presyntax.ConstantDefinition term -> do
      (term', type_) <- infer context term (InstantiateUntil Explicit) $ Lazy $ pure Nothing
      pure (Syntax.ConstantDefinition term', type_)

    Presyntax.DataDefinition params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs
      type' <- evaluate context type_
      pure (Syntax.DataDefinition tele, type')

inferDataDefinition
  :: Context v
  -> [(Name, Presyntax.Type)]
  -> [(Name.Constructor, Presyntax.Type)]
  -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v, Syntax.Type v)
inferDataDefinition context params constrs =
  case params of
    [] -> do
      constrs' <- forM constrs $ \(constr, type_) -> do
        -- TODO check return value of constructors
        type' <- check context type_ Builtin.type_
        pure (constr, type')
      pure
        ( Telescope.Empty (Syntax.ConstructorDefinitions constrs')
        , Syntax.Global Builtin.typeName
        )

    (name, type_):params' -> do
      type' <- check context type_ Builtin.type_
      type'' <- lazy $ evaluate context type'
      (context', _) <- Context.extend context name type''
      (tele, dataType) <- inferDataDefinition context' params' constrs
      pure
        ( Telescope.Extend name type' Explicit tele
        , Syntax.Pi name type' Explicit dataType
        )

-------------------------------------------------------------------------------

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context (Presyntax.Term span term) =
  checkUnspanned (Context.spanned span context) term

infer
  :: Context v
  -> Presyntax.Term
  -> InstantiateUntil
  -> Lazy (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
infer context (Presyntax.Term span term) =
  inferUnspanned (Context.spanned span context) term

checkUnspanned
  :: Context v
  -> Presyntax.UnspannedTerm
  -> Domain.Type
  -> M (Syntax.Term v)
checkUnspanned context term expectedType = do
  expectedType' <- Context.forceHead context expectedType
  case (term, expectedType') of
    (Presyntax.Let name term' body, _) -> do
      (term'', type_) <- infer context term' (InstantiateUntil Explicit) $ Lazy $ pure Nothing
      type' <- readback context type_

      term''' <- lazy $ evaluate context term''
      (context', _) <- Context.extendDef context name term''' $ Lazy $ pure type_

      body' <- check context' body expectedType
      pure $ Syntax.Let name term'' type' body'

    (Presyntax.Lam name plicity body, Domain.Pi _ source typePlicity domainClosure)
      | plicity == typePlicity -> do
        source' <- force source
        source'' <- readback context source'
        (context', var) <- Context.extend context name source

        domain <-
          Evaluation.evaluateClosure
            domainClosure
            (Lazy $ pure $ Domain.var var)
        body' <- check context' body domain
        pure $ Syntax.Lam name source'' plicity body'

    (Presyntax.Lam name Explicit body, Domain.Fun source domain) -> do
      source' <- force source
      source'' <- readback context source'
      (context', _) <- Context.extend context name source

      domain' <- force domain
      body' <- check context' body domain'
      pure $ Syntax.Lam name source'' Explicit body'

    (_, Domain.Pi name source Implicit domainClosure) -> do
      (context', v) <- Context.extend context name source
      domain <- Evaluation.evaluateClosure domainClosure (Lazy $ pure $ Domain.var v)
      source' <- force source
      source'' <- readback context source'
      term' <- checkUnspanned context' term domain
      pure $ Syntax.Lam name source'' Implicit term'

    (Presyntax.App function plicity argument, _) -> do
      expectedTypeName <- lazy $ getExpectedTypeName context expectedType'
      (function', functionType) <- infer context function (InstantiateUntil plicity) expectedTypeName
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ source typePlicity domainClosure
          | plicity == typePlicity -> do
            source' <- force source
            argument' <- check context argument source'
            argument'' <- lazy $ evaluate context argument'
            domain <- Evaluation.evaluateClosure domainClosure argument''
            Unification.unify context domain expectedType
            pure $ Syntax.App function' plicity argument'

        Domain.Fun source domain
          | plicity == Explicit -> do
            source' <- force source
            domain' <- force domain
            Unification.unify context domain' expectedType'
            argument' <- check context argument source'
            pure $ Syntax.App function' plicity argument'

        _ -> do
          source <- Context.newMetaType context
          metaFunctionType <-
            case plicity of
              Explicit ->
                pure $ Domain.Fun (Lazy $ pure source) (Lazy $ pure expectedType')

              Implicit -> do
                (context', _) <- Context.extend context "x" $ Lazy $ pure source
                expectedType'' <- readback context' expectedType'
                pure $
                  Domain.Pi "x" (Lazy $ pure source) Implicit $
                  Domain.Closure (Context.toEvaluationEnvironment context) expectedType''

          Unification.unify context functionType' metaFunctionType
          argument' <- check context argument source
          pure $ Syntax.App function' plicity argument'

    _ -> do
      expectedTypeName <- lazy $ getExpectedTypeName context expectedType'
      (term', type_) <- inferUnspanned context term (InstantiateUntil Explicit) expectedTypeName
      Unification.unify context type_ expectedType'
      pure term'

inferUnspanned
  :: Context v
  -> Presyntax.UnspannedTerm
  -> InstantiateUntil
  -> Lazy (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
inferUnspanned context term until expectedTypeName =
  case term of
    Presyntax.Var name ->
      insertMetasForImplicitsM context $
        inferName context name expectedTypeName

    Presyntax.Let name term' body -> do
      (term'', type_) <- infer context term' (InstantiateUntil Explicit) $ Lazy $ pure Nothing
      type' <- readback context type_

      term''' <- lazy $ evaluate context term''
      (context', _) <- Context.extendDef context name term''' $ Lazy $ pure type_

      (body', bodyType) <- infer context' body until expectedTypeName
      pure
        ( Syntax.Let name term'' type' body'
        , bodyType
        )

    Presyntax.Pi name plicity source domain -> do
      source' <- check context source Builtin.type_

      (context', _) <- Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      pure
        ( Syntax.Pi name source' plicity domain'
        , Builtin.type_
        )

    Presyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      pure
        ( Syntax.Fun source' domain'
        , Builtin.type_
        )

    Presyntax.Lam name plicity body ->
      insertMetasForImplicitsM context $ do
        source <- Context.newMetaType context
        source' <- readback context source
        (context', _) <- Context.extend context name $ Lazy $ pure source
        (body', domain) <- infer context' body (InstantiateUntil Explicit) $ Lazy $ pure Nothing
        domain' <- readback context' domain

        pure
          ( Syntax.Lam name source' plicity body'
          , Domain.Pi name (Lazy $ pure source) plicity
            $ Domain.Closure (Context.toEvaluationEnvironment context) domain'
          )

    Presyntax.App function plicity argument ->
      insertMetasForImplicitsM context $ do
        (function', functionType) <- infer context function (InstantiateUntil plicity) expectedTypeName
        functionType' <- Context.forceHead context functionType

        case functionType' of
          Domain.Pi _ source typePlicity domainClosure
            | plicity == typePlicity -> do
              source' <- force source
              argument' <- check context argument source'
              argument'' <- lazy $ evaluate context argument'
              domain <- Evaluation.evaluateClosure domainClosure argument''
              pure
                ( Syntax.App function' plicity argument'
                , domain
                )

          Domain.Fun source domain
            | plicity == Explicit -> do
              source' <- force source
              argument' <- check context argument source'
              domain' <- force domain
              pure
                ( Syntax.App function' plicity argument'
                , domain'
                )

          _ -> do
            source <- Context.newMetaType context
            domain <- Context.newMetaType context
            metaFunctionType <-
              case plicity of
                Explicit ->
                  pure $ Domain.Fun (Lazy $ pure source) (Lazy $ pure domain)

                Implicit -> do
                  (context', _) <- Context.extend context "x" $ Lazy $ pure source
                  domain' <- readback context' domain
                  pure $
                    Domain.Pi "x" (Lazy $ pure source) Implicit $
                    Domain.Closure (Context.toEvaluationEnvironment context) domain'

            Unification.unify context functionType' metaFunctionType
            argument' <- check context argument source
            pure
              ( Syntax.App function' plicity argument'
              , domain
              )

    Presyntax.Wildcard -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta type_ context
      term'' <- readback context term'
      pure (term'', type_)

    Presyntax.ParseError err -> do
      Context.reportParseError context err
      inferUnspanned context Presyntax.Wildcard until expectedTypeName

inferName :: Context v -> Name.Pre -> Lazy (Maybe Name.Qualified) -> M (Syntax.Term v, Domain.Type)
inferName context name expectedTypeName =
  case Context.lookupNameIndex name context of
    Just i -> do
      type_ <- force $ Context.lookupIndexType i context
      pure
        ( Syntax.Var i
        , type_
        )

    Nothing -> do
      maybeQualifiedName <-
        fetch $
          Query.ResolvedName
            (Context.scopeKey context)
            name
      case maybeQualifiedName of
        Nothing -> do
          Context.report context $ Error.NotInScope name
          fail

        Just (Scope.Name qualifiedName) -> do
          type_ <- fetch $ Query.ElaboratedType qualifiedName
          type' <- evaluate context $ Syntax.fromVoid type_
          pure
            ( Syntax.Global qualifiedName
            , type'
            )

        Just (Scope.Constructors (toList -> [constr])) ->
          constrSuccess constr

        Just (Scope.Constructors constrs) -> do
          maybeExpectedTypeName <- force expectedTypeName
          case maybeExpectedTypeName of
            Nothing -> do
              Context.report context $ Error.Ambiguous name constrs mempty
              fail
            Just typeName -> do
              let
                constrs' =
                  HashSet.filter
                    (\(Name.QualifiedConstructor constrTypeName _) -> constrTypeName == typeName)
                    constrs
              case toList constrs' of
                [constr] ->
                  constrSuccess constr

                _ -> do
                  Context.report context $ Error.Ambiguous name constrs' mempty
                  fail


        Just (Scope.Ambiguous constrCandidates nameCandidates) -> do
          Context.report context $ Error.Ambiguous name constrCandidates nameCandidates
          fail
  where
    constrSuccess constr = do
      type_ <- fetch $ Query.ConstructorType constr
      type' <- evaluate context $ Syntax.fromVoid type_
      pure
        ( Syntax.Con constr
        , type'
        )
    fail = do
      type_ <- Context.newMetaType context
      type' <- readback context type_
      pure
        ( Syntax.App (Syntax.Global Builtin.fail) Explicit type'
        , type_
        )

getExpectedTypeName
  :: Context v
  -> Domain.Type
  -> M (Maybe Name.Qualified)
getExpectedTypeName context type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Neutral (Domain.Global name) _ ->
      pure $ Just name

    Domain.Neutral {} ->
      pure Nothing

    Domain.Pi name source _ domainClosure -> do
      (context', var) <- Context.extend context name source
      domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure $ Domain.var var
      getExpectedTypeName context' domain

    Domain.Fun _ domain -> do
      domain' <- force domain
      getExpectedTypeName context domain'

    Domain.Lam {} ->
      pure Nothing

-------------------------------------------------------------------------------
-- Implicits

insertMetasForImplicitsM
  :: Context v
  -> M (Syntax.Term v, Domain.Type)
  -> M (Syntax.Term v, Domain.Type)
insertMetasForImplicitsM context m = do
  (term, type_) <- m
  insertMetasForImplicits context term type_

insertMetasForImplicits
  :: Context v
  -> Syntax.Term v
  -> Domain.Type
  -> M (Syntax.Term v, Domain.Type)
insertMetasForImplicits context term type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Pi _ source Implicit domainClosure -> do
      source' <- force source
      meta <- Context.newMeta source' context
      domain <- Evaluation.evaluateClosure domainClosure (Lazy $ pure meta)
      meta' <- readback context meta
      insertMetasForImplicits context (Syntax.App term Implicit meta') domain

    _ ->
      pure (term, type')

-------------------------------------------------------------------------------
-- Meta solutions

checkMetaSolutions
  :: Context v
  -> M Syntax.MetaSolutions
checkMetaSolutions context = do
  metaVars <- liftIO $ readIORef $ Context.metas context
  flip IntMap.traverseWithKey (Meta.vars metaVars) $ \index var ->
    case var of
      Meta.Unsolved type_ span -> do
        Context.report (Context.spanned span context) $
          Error.UnsolvedMetaVariable index
        pure (Syntax.App (Syntax.Global Builtin.fail) Explicit type_, type_)

      Meta.Solved solution type_ ->
        pure (solution, type_)

-------------------------------------------------------------------------------

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEvaluationEnvironment context)

readback :: Context v -> Domain.Value -> M (Syntax.Term v)
readback context =
  Readback.readback (Context.toReadbackEnvironment context)
