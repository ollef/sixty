{-# language DeriveFunctor #-}
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

data Inferred term
  = Inferred term !(Lazy Domain.Type)
  deriving Functor

newtype Checked term
  = Checked term
  deriving Functor

newtype InstantiateUntil = InstantiateUntil Plicity

data Expected f where
  Infer :: InstantiateUntil -> Expected Inferred
  Check :: Domain.Type -> Expected Checked

-------------------------------------------------------------------------------

inferDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> M ((Syntax.Definition, Syntax.Type Void), [Error])
inferDefinition key def = do
  context <- Context.empty key
  Inferred def' typeValue <- elaborateDefinition context def (Infer (InstantiateUntil Explicit))
  typeValue' <- force typeValue
  type_ <- readback context typeValue'
  metas <- checkMetaSolutions context
  result <- Metas.inlineSolutions metas def' type_
  errors <- liftIO $ readIORef (Context.errors context)
  pure (result, toList errors)

checkDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> Domain.Type
  -> M (Syntax.Definition, [Error])
checkDefinition key def type_ = do
  context <- Context.empty key
  Checked def' <- elaborateDefinition context def $ Check type_
  metas <- checkMetaSolutions context
  (def'', _) <- Metas.inlineSolutions metas def' $ Syntax.Global Builtin.fail
  errors <- liftIO $ readIORef (Context.errors context)
  pure (def'', toList errors)

elaborateDefinition
  :: Functor e
  => Context Void
  -> Presyntax.Definition
  -> Expected e
  -> M (e Syntax.Definition)
elaborateDefinition context def expected =
  case def of
    Presyntax.TypeDeclaration type_ -> do
      type' <- elaborate context type_ expected
      pure $ Syntax.TypeDeclaration <$> type'

    Presyntax.ConstantDefinition term -> do
      term' <- elaborate context term expected
      pure $ Syntax.ConstantDefinition <$> term'

    Presyntax.DataDefinition params constrs ->
      case expected of
        -- TODO: use `until`
        Infer _until -> do
          (tele, type_) <- inferDataDefinition context params constrs
          type' <- lazy $ evaluate context type_
          pure $ Inferred (Syntax.DataDefinition tele) type'

        Check expectedType -> do
          (tele, type_) <- inferDataDefinition context params constrs
          type' <- evaluate context type_
          Unification.unify context type' expectedType
          pure $ Checked (Syntax.DataDefinition tele)

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
check context term type_ =
  case (term, type_) of
    (Presyntax.Term _ (Presyntax.Lam _ Implicit _), Domain.Pi _ _ Implicit _) -> do
      Checked result <- elaborate context term $ Check type_
      pure result
    (_, Domain.Pi n s Implicit c) -> do
      (context', v) <- Context.extend context n s
      d' <- Evaluation.evaluateClosure c (Lazy . pure $ Domain.var v)
      s' <- force s
      t <- readback context s'
      term' <- check context' term d'
      pure $ Syntax.Lam n t Implicit term'
    _ -> do
      Checked result <- elaborate context term $ Check type_
      pure result

infer
  :: Context v
  -> Presyntax.Term
  -> InstantiateUntil
  -> M (Inferred (Syntax.Term v))
infer context term until =
  elaborate context term (Infer until)

elaborated
  :: Context v
  -> Expected e
  -> Syntax.Term v
  -> Lazy Domain.Type
  -> M (e (Syntax.Term v))
elaborated context expected term type_ =
  case expected of
    Infer (InstantiateUntil Explicit) -> do
      type' <- force type_
      insertMetasForImplicits context term type'

    Infer (InstantiateUntil Implicit) ->
      pure $ Inferred term type_

    Check expectedType -> do
      type' <- force type_
      Unification.unify context type' expectedType
      pure $ Checked term

insertMetasForImplicits :: Context v -> Syntax.Term v -> Domain.Type -> M (Inferred (Syntax.Term v))
insertMetasForImplicits context term type_ = do
  case type_ of
    Domain.Pi _ sourceType Implicit domainClosure -> do
      sourceType' <- force sourceType
      meta <- Context.newMeta sourceType' context
      domain <- Evaluation.evaluateClosure domainClosure (Lazy $ pure meta)
      meta' <- readback context meta
      insertMetasForImplicits context (Syntax.App term Implicit meta') domain
    _ ->
      pure $ Inferred term (Lazy (pure type_))

elaborate
  :: Functor e
  => Context v
  -> Presyntax.Term
  -> Expected e
  -> M (e (Syntax.Term v))
elaborate context (Presyntax.Term span term) =
  elaborateUnspanned (Context.spanned span context) term

elaborateUnspanned
  :: Functor e
  => Context v
  -> Presyntax.UnspannedTerm
  -> Expected e
  -> M (e (Syntax.Term v))
elaborateUnspanned context term expected = -- trace ("elaborate " <> show term :: Text) $
  case term of
    Presyntax.Var name ->
      case Context.lookupNameIndex name context of
        Nothing -> do
          maybeQualifiedName <-
            fetch $
              Query.ResolvedName
                (Context.scopeKey context)
                name
          case maybeQualifiedName of
            Nothing -> do
              Context.report context $ Error.NotInScope name
              resultType <- Context.newMetaType context
              resultType' <- readback context resultType
              elaborated
                context
                expected
                (Syntax.App (Syntax.Global Builtin.fail) Explicit resultType')
                (Lazy $ pure resultType)

            Just (Scope.Name qualifiedName) -> do
              type_ <- fetch $ Query.ElaboratedType qualifiedName
              type' <- lazy $ evaluate context $ Syntax.fromVoid type_
              elaborated
                context
                expected
                (Syntax.Global qualifiedName)
                type'


            Just (Scope.Constructors (toList -> [constr])) -> do
              type_ <- fetch $ Query.ConstructorType constr
              type' <- evaluate context $ Syntax.fromVoid type_
              elaborated
                context
                expected
                (Syntax.Con constr)
                (Lazy $ pure type')

            Just (Scope.Constructors constrs) -> do
              -- TODO
              Context.report context $ Error.Ambiguous name constrs mempty
              resultType <- Context.newMetaType context
              resultType' <- readback context resultType
              elaborated
                context
                expected
                (Syntax.App (Syntax.Global Builtin.fail) Explicit resultType')
                (Lazy $ pure resultType)

            Just (Scope.Ambiguous constrCandidates nameCandidates) -> do
              Context.report context $ Error.Ambiguous name constrCandidates nameCandidates
              resultType <- Context.newMetaType context
              resultType' <- readback context resultType
              elaborated
                context
                expected
                (Syntax.App (Syntax.Global Builtin.fail) Explicit resultType')
                (Lazy $ pure resultType)


        Just i ->
          elaborated
            context
            expected
            (Syntax.Var i)
            (Context.lookupIndexType i context)

    Presyntax.Let name term' body -> do
      Inferred term'' type_ <- infer context term' (InstantiateUntil Implicit)
      type' <- force type_
      type'' <- readback context type'

      term''' <- lazy $ evaluate context term''
      (context', _) <- Context.extendDef context name term''' $ Lazy $ pure type'

      body' <- elaborate context' body expected
      pure $ Syntax.Let name term'' type'' <$> body'

    Presyntax.Pi name plicity source domain -> do
      source' <- check context source Builtin.type_

      (context', _) <- Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      elaborated
        context
        expected
        (Syntax.Pi name source' plicity domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      elaborated
        context
        expected
        (Syntax.Fun source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Lam name plicity body ->
      let
        inferIt = do
          source <- Context.newMetaType context
          source' <- readback context source
          (context', _) <- Context.extend context name (Lazy $ pure source)
          Inferred body' domain <- infer context' body (InstantiateUntil Explicit)
          type_ <- lazy $ do
            domain' <- force domain
            domain'' <- readback context' domain'
            pure
              $ Domain.Pi name (Lazy $ pure source)
              plicity
              $ Domain.Closure (Context.toEvaluationEnvironment context) domain''

          elaborated
            context
            expected
            (Syntax.Lam name source' plicity body')
            type_
      in
      case expected of
        -- TODO: use `until`
        Infer _until ->
          inferIt

        Check expectedType -> do
          expectedType' <- Context.forceHead context expectedType
          case expectedType' of
            Domain.Pi _ source typePlicity domainClosure
              | plicity == typePlicity -> do
              source' <- force source
              source'' <- readback context source'
              (context', var) <- Context.extend context name source

              domain <-
                Evaluation.evaluateClosure
                  domainClosure
                  (Lazy $ pure $ Domain.var var)
              body' <- check context' body domain
              pure $ Checked (Syntax.Lam name source'' plicity body')

            Domain.Fun source domain
              | plicity == Explicit -> do
              source' <- force source
              source'' <- readback context source'
              (context', _) <- Context.extend context name source

              domain' <- force domain
              body' <- check context' body domain'
              pure $ Checked (Syntax.Lam name source'' Explicit body')

            _ ->
              inferIt

    Presyntax.App function plicity argument -> do
      Inferred function' functionType <- infer context function (InstantiateUntil plicity)
      functionType' <- force functionType
      functionType'' <- Context.forceHead context functionType'

      case functionType'' of
        Domain.Pi _ source typePlicity domainClosure
          | plicity == typePlicity -> do
          source' <- force source
          argument' <- check context argument source'
          argument'' <- lazy $ evaluate context argument'
          domain <- lazy $ Evaluation.evaluateClosure domainClosure argument''
          elaborated
            context
            expected
            (Syntax.App function' plicity argument')
            domain

        Domain.Fun source domain
          | plicity == Explicit -> do
          source' <- force source
          case expected of
            Check expectedType -> do
              domain' <- force domain
              Unification.unify context expectedType domain'
              argument' <- check context argument source'
              pure $ Checked (Syntax.App function' plicity argument')

            -- TODO: use `until`
            Infer _until -> do
              argument' <- check context argument source'
              pure $ Inferred (Syntax.App function' plicity argument') domain

        _ | plicity == Explicit -> do
          source <- Context.newMetaType context
          domain <- Context.newMetaType context
          let
            lazySource = Lazy (pure source)
            lazyDomain = Lazy (pure domain)
            metaFunctionType = Domain.Fun lazySource (Lazy (pure domain))

          Unification.unify context functionType'' metaFunctionType
          case expected of
            Check expectedType -> do
              Unification.unify context expectedType domain
              argument' <- check context argument source
              pure $ Checked (Syntax.App function' plicity argument')

            -- TODO: use `until`
            Infer _until -> do
              argument' <- check context argument source
              pure $ Inferred (Syntax.App function' plicity argument') lazyDomain

        _ ->
            panic "The “impossible” happened :S"

    Presyntax.Wildcard -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta type_ context
      term'' <- readback context term'
      elaborated context expected term'' $ Lazy $ pure type_

    Presyntax.ParseError err -> do
      Context.reportParseError context err
      elaborateUnspanned context Presyntax.Wildcard expected

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
