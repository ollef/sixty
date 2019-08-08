{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language ScopedTypeVariables #-}
module Elaboration where

import Protolude hiding (Seq, force, check, evaluate, until)

import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef
import Data.Text.Prettyprint.Doc (Doc)
import Rock

import qualified Builtin
import Context (Context)
import qualified Context
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Elaboration.Clauses as Clauses
import qualified Elaboration.Matching as Matching
import qualified Elaboration.Metas as Metas
import Error (Error)
import qualified Error
import qualified Evaluation
import Index
import qualified Inlining
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Presyntax
import qualified Pretty
import qualified "this" Data.IntMap as IntMap
import qualified Query
import qualified Readback
import qualified Scope
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified Unification
import Var (Var)

inferTopLevelDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> M ((Syntax.Definition, Syntax.Type Void), [Error])
inferTopLevelDefinition key def = do
  context <- Context.empty key
  (def', typeValue) <- inferDefinition context def
  type_ <- readback context typeValue
  metas <- checkMetaSolutions context
  (def'', type') <- Metas.inlineSolutions metas def' type_
  def''' <- Inlining.inlineDefinition def''
  type'' <- Inlining.inlineTerm Inlining.empty type'
  errors <- liftIO $ readIORef (Context.errors context)
  pure ((def''', type''), toList errors)

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
  def''' <- Inlining.inlineDefinition def''
  errors <- liftIO $ readIORef $ Context.errors context
  pure (def''', toList errors)

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

    Presyntax.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | clause <- clauses]
      term' <- Clauses.check context clauses' expectedType
      pure $ Syntax.ConstantDefinition term'

    Presyntax.DataDefinition params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs mempty
      type' <- evaluate context type_
      success <- Context.try_ context $ Unification.unify context type' expectedType
      if success then
        pure $ Syntax.DataDefinition tele

      else do
        expectedType' <- readback context expectedType
        pure $
          Syntax.ConstantDefinition $
          Syntax.App (Syntax.Global Builtin.fail) Explicit expectedType'

inferDefinition
  :: Context Void
  -> Presyntax.Definition
  -> M (Syntax.Definition, Domain.Type)
inferDefinition context def =
  case def of
    Presyntax.TypeDeclaration type_ -> do
      type' <- check context type_ Builtin.type_
      pure (Syntax.TypeDeclaration type', Builtin.type_)

    Presyntax.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | clause <- clauses]
      (term', type_) <- Clauses.infer context clauses'
      pure (Syntax.ConstantDefinition term', type_)

    Presyntax.DataDefinition params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs mempty
      type' <- evaluate context type_
      pure (Syntax.DataDefinition tele, type')

-------------------------------------------------------------------------------

inferDataDefinition
  :: Context v
  -> [(Name, Presyntax.Type, Plicity)]
  -> [([Name.Constructor], Presyntax.Type)]
  -> Tsil (Plicity, Var)
  -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v, Syntax.Type v)
inferDataDefinition context preParams constrs paramVars =
  case preParams of
    [] -> do
      let
        Scope.KeyedName _ qualifiedThisName@(Name.Qualified _ thisName) =
          Context.scopeKey context

        this =
          Syntax.Global qualifiedThisName

      thisType <-
        Syntax.fromVoid <$>
          varPis
            context
            (Domain.empty $ Context.scopeKey context)
            (toList paramVars)
            Builtin.type_

      thisType' <- evaluate context thisType

      (context', var) <- Context.extend context thisName $ Lazy $ pure thisType'

      constrs' <- forM constrs $ \(cs, type_) -> do
        type' <- checkConstructorType context' type_ var paramVars
        pure [(constr, Syntax.Let thisName this thisType type') | constr <- cs]
      pure
        ( Telescope.Empty (Syntax.ConstructorDefinitions $ concat constrs')
        , Syntax.Global Builtin.typeName
        )

    (name, type_, plicity):preParams' -> do
      type' <- check context type_ Builtin.type_
      type'' <- lazy $ evaluate context type'
      (context', paramVar) <- Context.extend context name type''
      let
        paramVars' =
          paramVars Tsil.:> (plicity, paramVar)
      (tele, dataType) <- inferDataDefinition context' preParams' constrs paramVars'
      pure
        ( Telescope.Extend name type' plicity tele
        , Syntax.Pi name type' plicity dataType
        )

varPis
  :: Context v
  -> Domain.Environment v'
  -> [(Plicity, Var)]
  -> Domain.Value
  -> M (Syntax.Term v')
varPis context env vars domain =
  case vars of
    [] ->
      Readback.readback (Readback.fromEvaluationEnvironment env) domain

    (plicity, var):vars'-> do
      let
        env' =
          Domain.extendVar env var
      source <- force $ Context.lookupVarType var context
      source' <- Readback.readback (Readback.fromEvaluationEnvironment env) source
      domain' <- varPis context env' vars' domain
      pure $ Syntax.Pi (Context.lookupVarName var context) source' plicity domain'

checkConstructorType
  :: Context v
  -> Presyntax.Term
  -> Var
  -> Tsil (Plicity, Var)
  -> M (Syntax.Term v)
checkConstructorType context term@(Presyntax.Term span _) dataVar paramVars = do
  let
    context' =
      Context.spanned span context
  constrType <- check context' term Builtin.type_
  constrType' <- evaluate context' constrType
  maybeConstrType'' <- Context.try context' $ go context' constrType'
  pure $ case maybeConstrType'' of
    Nothing ->
      Syntax.App (Syntax.Global Builtin.fail) Explicit (Syntax.Global Builtin.typeName)

    Just constrType'' ->
      constrType''
  where
    go :: Context v -> Domain.Value -> M (Syntax.Term v)
    go context' constrType = do
      constrType' <- Context.forceHead context constrType
      case constrType' of
        Domain.Pi name source plicity domainClosure -> do
          source' <- force source
          source'' <- readback context' source'
          (context'', var) <- Context.extendUnnamed context' name source
          domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure $ Domain.var var
          domain' <- go context'' domain
          pure $ Syntax.Pi name source'' plicity domain'

        Domain.Fun source domain -> do
          source' <- force source
          source'' <- readback context' source'
          domain' <- force domain
          domain'' <- go context' domain'
          pure $ Syntax.Fun source'' domain''

        Domain.Neutral (Domain.Var headVar) indices
          | headVar == dataVar ->
            indexEqualities context' (toList indices) (toList paramVars)

        _ -> do
          Unification.unify
            context'
            constrType'
            (Domain.Neutral
              (Domain.Var dataVar)
              ((\(plicity, var) -> (plicity, Lazy $ pure $ Domain.var var)) <$> paramVars))
          readback context' constrType'

    indexEqualities
      :: Context v
      -> [(Plicity, Lazy Domain.Value)]
      -> [(Plicity, Var)]
      -> M (Syntax.Term v)
    indexEqualities context' indices paramVars' =
      case (indices, paramVars') of
        ((plicity1, index):indices', (plicity2, paramVar):paramVars'')
          | plicity1 == plicity2 -> do
            index' <- force index
            index'' <- Context.forceHead context' index'
            case index'' of
              Domain.Neutral (Domain.Var indexVar) Tsil.Empty
                | indexVar == paramVar ->
                  indexEqualities context' indices' paramVars''

              _ -> do
                let
                  source =
                    Builtin.Equals
                      (Context.lookupVarType paramVar context')
                      index
                      (Lazy $ pure $ Domain.var paramVar)

                source' <- readback context' source

                (context'', _) <- Context.extendUnnamed context' "eq" $ Lazy $ pure source
                domain <- indexEqualities context'' indices' paramVars''
                pure $ Syntax.Pi "eq" source' Constraint domain

          | otherwise ->
            panic "indexEqualities plicity mismatch"

        ([], []) ->
          readback context' $
            Domain.Neutral (Domain.Var dataVar) $
            second (Lazy . pure . Domain.var) <$> paramVars

        _ ->
          panic "indexEqualities length mismatch"

-------------------------------------------------------------------------------

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context (Presyntax.Term span term) =
  -- traceShow ("check", term) $
  checkUnspanned (Context.spanned span context) term

-- check context (Presyntax.Term span term) type_ = do
--   result <- checkUnspanned (Context.spanned span context) term type_
--   prettyType <- prettyValue context type_
--   putText ""
--   putText "check"
--   putText $ "    " <> show term
--   putText $ "    " <> show prettyType
--   putText $ "  = " <> show (prettyTerm context result)
--   pure result

infer
  :: Context v
  -> Presyntax.Term
  -> M (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
infer context (Presyntax.Term span term) =
  -- traceShow ("infer", term) $
  inferUnspanned (Context.spanned span context) term

-- infer context (Presyntax.Term span term) expectedTypeName = do
--   (term', type_) <- inferUnspanned (Context.spanned span context) term expectedTypeName
--   prettyType <- prettyValue context type_
--   putText ""
--   putText "infer"
--   putText $ "    " <> show term
--   putText $ "  = " <> show (prettyTerm context term')
--   putText $ "  , " <> show prettyType
--   pure (term', type_)

checkUnspanned
  :: Context v
  -> Presyntax.UnspannedTerm
  -> Domain.Type
  -> M (Syntax.Term v)
checkUnspanned context term expectedType = do
  expectedType' <- Context.forceHead context expectedType
  case (term, expectedType') of
    (Presyntax.Let name term' body, _) -> do
      (context', term'', type_) <- elaborateLet context name term'
      body' <- check context' body expectedType'
      pure $ Syntax.Let name term'' type_ body'

    (Presyntax.Case scrutinee branches, _) -> do
      (scrutinee', scrutineeType) <-
        insertMetasM context UntilExplicit $ infer context scrutinee $ pure Nothing
      Matching.elaborateCase context scrutinee' scrutineeType branches expectedType'

    (Presyntax.Lam (Presyntax.ExplicitPattern pat) body, Domain.Pi name source Explicit domainClosure) ->
      checkLambda context name source Explicit pat domainClosure body

    (Presyntax.Lam (Presyntax.ExplicitPattern pat) body, Domain.Fun source domain) -> do
      source' <- force source
      source'' <- readback context source'
      (context', var) <- Context.extendUnnamed context "x" source
      domain' <- force domain
      body' <- Matching.elaborateSingle context' var pat body domain'
      pure $ Syntax.Lam "x" source'' Explicit body'

    (Presyntax.Lam (Presyntax.ImplicitPattern _ namedPats) body, _)
      | HashMap.null namedPats ->
        check context body expectedType'

    (Presyntax.Lam (Presyntax.ImplicitPattern span namedPats) body, Domain.Pi name source Implicit domainClosure)
      | name `HashMap.member` namedPats -> do
        let
          pat =
            namedPats HashMap.! name

          body' =
            Presyntax.Term (Context.span context) $
              Presyntax.Lam (Presyntax.ImplicitPattern span (HashMap.delete name namedPats)) body
        checkLambda context name source Implicit pat domainClosure body'

    (_, Domain.Pi name source Implicit domainClosure) -> do
      (context', v) <- Context.extendUnnamed context name source
      domain <- Evaluation.evaluateClosure domainClosure (Lazy $ pure $ Domain.var v)
      source' <- force source
      source'' <- readback context source'
      term' <- checkUnspanned context' term domain
      pure $ Syntax.Lam name source'' Implicit term'

    (Presyntax.App function argument, _) -> do
      let
        expectedTypeName =
          getExpectedTypeName context expectedType'
      (function', functionType) <-
        insertMetasM context UntilExplicit $ infer context function expectedTypeName
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ source Explicit domainClosure -> do
          (argument', domain) <- checkApplication context argument source domainClosure
          f <- subtype context domain expectedType'
          pure $ f $ Syntax.App function' Explicit argument'

        Domain.Fun source domain -> do
          source' <- force source
          domain' <- force domain
          f <- subtype context domain' expectedType'
          argument' <- check context argument source'
          pure $ f $ Syntax.App function' Explicit argument'

        _ -> do
          source <- Context.newMetaType context
          domain <- Context.newMetaType context
          let
            metaFunctionType =
              Domain.Fun (Lazy $ pure source) (Lazy $ pure expectedType')
          f <- Unification.tryUnify context functionType' metaFunctionType
          g <- subtype context domain expectedType'
          argument' <- check context argument source
          pure $ g $ Syntax.App (f function') Explicit argument'

    (Presyntax.ImplicitApps function arguments, _)
      | HashMap.null arguments ->
        check context function expectedType'

    (Presyntax.Wildcard, _) -> do
      term' <- Context.newMeta expectedType' context
      readback context term'

    (Presyntax.ParseError err, _) -> do
      Context.reportParseError context err
      checkUnspanned context Presyntax.Wildcard expectedType'

    _ -> do
      let
        expectedTypeName =
          getExpectedTypeName context expectedType'
      (term', type_) <- inferUnspanned context term expectedTypeName
      f <- subtype context type_ expectedType'
      pure $ f term'

inferUnspanned
  :: Context v
  -> Presyntax.UnspannedTerm
  -> M (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
inferUnspanned context term expectedTypeName =
  case term of
    Presyntax.Var name ->
      inferName context name expectedTypeName

    Presyntax.Let name term' body -> do
      (context', term'', type_) <- elaborateLet context name term'
      (body', bodyType) <- infer context' body expectedTypeName
      pure (Syntax.Let name term'' type_ body', bodyType)

    Presyntax.Pi name plicity source domain -> do
      source' <- check context source Builtin.type_
      source'' <- lazy $ evaluate context source'

      (context', _) <- Context.extend context name source''

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

    Presyntax.Lam (Presyntax.ExplicitPattern pat) body ->
      inferLambda context "x" Explicit pat body

    Presyntax.Lam (Presyntax.ImplicitPattern span argumentNames) body ->
      case HashMap.toList argumentNames of
        [] ->
          infer context body expectedTypeName

        [(name, pat)] ->
          inferLambda context name Implicit pat body

        _ -> do
          Context.report (Context.spanned span context) Error.UnableToInferImplicitLambda
          inferenceFailed context

    Presyntax.App function argument -> do
      (function', functionType) <-
        insertMetasM context UntilExplicit $ infer context function expectedTypeName
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ source Explicit domainClosure -> do
          (argument', domain) <- checkApplication context argument source domainClosure
          pure
            ( Syntax.App function' Explicit argument'
            , domain
            )

        Domain.Fun source domain -> do
          source' <- force source
          argument' <- check context argument source'
          domain' <- force domain
          pure
            ( Syntax.App function' Explicit argument'
            , domain'
            )

        _ -> do
          source <- Context.newMetaType context
          domain <- Context.newMetaType context
          let
            metaFunctionType =
              Domain.Fun (Lazy $ pure source) (Lazy $ pure domain)

          f <- Unification.tryUnify context functionType' metaFunctionType
          argument' <- check context argument source
          pure
            ( Syntax.App (f function') Explicit argument'
            , domain
            )

    Presyntax.ImplicitApps function arguments -> do
      (function', functionType) <-
        insertMetasM context (UntilImplicit (`HashMap.member` arguments)) $ infer context function expectedTypeName
      go function' arguments functionType

      where
        go function' arguments' functionType
          | HashMap.null arguments' =
            pure (function', functionType)

          | otherwise = do
            (metaArgs, functionType') <-
              insertMetas context (UntilImplicit (`HashMap.member` arguments')) mempty functionType

            let
              function'' =
                Syntax.apps function' metaArgs
            case functionType' of
              Domain.Pi name source Implicit domainClosure
                | name `HashMap.member` arguments' -> do
                  source' <- force source
                  argument' <- check context (arguments' HashMap.! name) source'
                  argument'' <- lazy $ evaluate context argument'
                  domain <- Evaluation.evaluateClosure domainClosure argument''
                  go
                    (Syntax.App function'' Implicit argument')
                    (HashMap.delete name arguments')
                    domain
              _
                | [(name, argument)] <- HashMap.toList arguments' -> do
                  source <- Context.newMetaType context
                  domain <- Context.newMetaType context
                  (context', _) <- Context.extend context name $ Lazy $ pure source
                  domain' <- readback context' domain
                  let
                    metaFunctionType =
                      Domain.Pi name (Lazy $ pure source) Implicit $
                      Domain.Closure (Context.toEvaluationEnvironment context) domain'
                  f <- Unification.tryUnify context functionType' metaFunctionType
                  argument' <- check context argument source
                  pure (Syntax.App (f function'') Implicit argument', domain)

              _ -> do
                Context.report context $ Error.ImplicitApplicationMismatch $ void arguments'
                inferenceFailed context

    Presyntax.Case scrutinee branches -> do
      (scrutinee', scrutineeType) <-
        insertMetasM context UntilExplicit $ infer context scrutinee $ pure Nothing
      type_ <- Context.newMetaType context
      term' <- Matching.elaborateCase context scrutinee' scrutineeType branches type_
      pure (term', type_)

    Presyntax.Wildcard -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta type_ context
      term'' <- readback context term'
      pure (term'', type_)

    Presyntax.ParseError err -> do
      Context.reportParseError context err
      inferUnspanned context Presyntax.Wildcard expectedTypeName

inferName
  :: Context v
  -> Name.Pre
  -> M (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
inferName context name expectedTypeName =
  case Context.lookupNameVar name context of
    Just var -> do
      term <- readback context (Domain.var var)
      type_ <- force $ Context.lookupVarType var context
      pure
        ( term
        , type_
        )

    Nothing -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) name

      case maybeScopeEntry of
        Nothing -> do
          Context.report context $ Error.NotInScope name
          inferenceFailed context

        Just (Scope.Name qualifiedName) -> do
          type_ <- fetch $ Query.ElaboratedType qualifiedName
          type' <- evaluate context $ Syntax.fromVoid type_
          pure
            ( Syntax.Global qualifiedName
            , type'
            )

        Just (Scope.Constructors candidates) -> do
          maybeConstr <- resolveConstructor context name candidates expectedTypeName
          case maybeConstr of
            Nothing ->
              inferenceFailed context

            Just constr -> do
              type_ <- fetch $ Query.ConstructorType constr
              type' <- evaluate context $ Syntax.fromVoid $ Telescope.fold Syntax.implicitPi type_
              pure
                ( Syntax.Con constr
                , type'
                )

        Just (Scope.Ambiguous constrCandidates nameCandidates) -> do
          Context.report context $ Error.Ambiguous name constrCandidates nameCandidates
          inferenceFailed context

inferenceFailed :: Context v -> M (Syntax.Term v, Domain.Type)
inferenceFailed context = do
  type_ <- Context.newMetaType context
  type' <- readback context type_
  pure
    ( Syntax.App (Syntax.Global Builtin.fail) Explicit type'
    , type_
    )

checkLambda
  :: Context v
  -> Name
  -> Lazy Domain.Type
  -> Plicity
  -> Presyntax.Pattern
  -> Domain.Closure
  -> Presyntax.Term
  -> M (Syntax.Term v)
checkLambda context name source plicity pat domainClosure body = do
  (context', var) <- Context.extendUnnamed context name source
  source' <- force source
  source'' <- readback context source'
  domain <-
    Evaluation.evaluateClosure
      domainClosure
      (Lazy $ pure $ Domain.var var)
  body' <- Matching.elaborateSingle context' var pat body domain
  pure $ Syntax.Lam name source'' plicity body'

inferLambda
  :: Context v
  -> Name
  -> Plicity
  -> Presyntax.Pattern
  -> Presyntax.Term
  -> M (Syntax.Term v, Domain.Type)
inferLambda context name plicity pat body = do
  source <- Context.newMetaType context
  source' <- readback context source
  (context', var) <- Context.extendUnnamed context name $ Lazy $ pure source
  domain <- Context.newMetaType context'
  body' <- Matching.elaborateSingle context' var pat body domain
  domain' <- readback context' domain

  pure
    ( Syntax.Lam name source' plicity body'
    , Domain.Pi name (Lazy $ pure source) plicity
      $ Domain.Closure (Context.toEvaluationEnvironment context) domain'
    )

checkApplication
  :: Context v
  -> Presyntax.Term
  -> Lazy Domain.Type
  -> Domain.Closure
  -> M (Syntax.Term v, Domain.Value)
checkApplication context argument source domainClosure = do
  source' <- force source
  argument' <- check context argument source'
  argument'' <- lazy $ evaluate context argument'
  domain <- Evaluation.evaluateClosure domainClosure argument''
  pure (argument', domain)

elaborateLet
  :: Context v
  -> Name
  -> Presyntax.Term
  -> M (Context (Succ v), Syntax.Term v, Syntax.Type v)
elaborateLet context name term = do
  (term', type_) <-
    insertMetasM context UntilExplicit $ infer context term $ pure Nothing
  type' <- readback context type_
  term'' <- lazy $ evaluate context term'
  (context', _) <- Context.extendDef context name term'' $ Lazy $ pure type_
  pure (context', term', type')

resolveConstructor
  :: Context v
  -> Name.Pre
  -> HashSet Name.QualifiedConstructor
  -> M (Maybe Name.Qualified)
  -> M (Maybe Name.QualifiedConstructor)
resolveConstructor context name candidates expectedTypeName =
  case toList candidates of
    [constr] ->
      pure $ Just constr

    _ -> do
      maybeExpectedTypeName <- expectedTypeName
      case maybeExpectedTypeName of
        Nothing -> do
          Context.report context $ Error.Ambiguous name candidates mempty
          pure Nothing

        Just typeName -> do
          let
            constrs' =
              HashSet.filter
                (\(Name.QualifiedConstructor constrTypeName _) -> constrTypeName == typeName)
                candidates
          case toList constrs' of
            [constr] ->
              pure $ Just constr

            _ -> do
              Context.report context $ Error.Ambiguous name constrs' mempty
              pure Nothing

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
      (context', var) <- Context.extendUnnamed context name source
      domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure $ Domain.var var
      getExpectedTypeName context' domain

    Domain.Fun _ domain -> do
      domain' <- force domain
      getExpectedTypeName context domain'

    Domain.Lam {} ->
      pure Nothing

    Domain.Case {} ->
      pure Nothing

-------------------------------------------------------------------------------
-- Implicits

data InsertUntil where
  UntilExplicit :: InsertUntil
  UntilImplicit :: (Name -> Bool) -> InsertUntil

insertMetasM
  :: Context v
  -> InsertUntil
  -> M (Syntax.Term v, Domain.Type)
  -> M (Syntax.Term v, Domain.Type)
insertMetasM context until m = do
  (term, type_) <- m
  (args, type') <- insertMetas context until mempty type_
  pure (Syntax.apps term args, type')

insertMetas
  :: Context v
  -> InsertUntil
  -> [(Plicity, Syntax.Term v)]
  -> Domain.Type
  -> M ([(Plicity, Syntax.Term v)], Domain.Type)
insertMetas context until args type_ = do
  type' <- Context.forceHead context type_
  case (until, type') of
    (UntilExplicit, Domain.Pi _ source Implicit domainClosure) ->
      instantiate source domainClosure

    (UntilImplicit stopAt, Domain.Pi name source Implicit domainClosure)
      | not $ stopAt name ->
        instantiate source domainClosure

    (_, Domain.Pi _ source Constraint domainClosure) -> do
      source' <- force source
      source'' <- Context.forceHead context source'
      case source'' of
        Builtin.Equals kind term1 term2 -> do
          term1' <- force term1
          term2' <- force term2
          f <- Unification.tryUnify context term1' term2'
          let
            value =
              Builtin.Refl kind term1 term2
          domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure value
          value' <- readback context value
          insertMetas context until ((Constraint, f value') : args) domain

        _ ->
          panic "insertMetas: non-equality constraint"

    _ ->
      pure (args, type')
  where
    instantiate source domainClosure = do
      source' <- force source
      meta <- Context.newMeta source' context
      domain <- Evaluation.evaluateClosure domainClosure (Lazy $ pure meta)
      meta' <- readback context meta
      insertMetas context until ((Implicit, meta') : args) domain

subtype
  :: Context v
  -> Domain.Type
  -> Domain.Type
  -> M (Syntax.Term v -> Syntax.Term v)
subtype context type1 type2 = do
  type1' <- Context.forceHead context type1
  type2' <- Context.forceHead context type2
  let
    until =
      case type2' of
        Domain.Pi _ _ Implicit _ ->
          UntilImplicit $ const True

        Domain.Neutral (Domain.Meta _) _ ->
          UntilImplicit $ const True

        _ ->
          UntilExplicit

  (args, type1'') <- insertMetas context until mempty type1'
  f <- Unification.tryUnify context type1'' type2'
  pure $ \term -> f $ Syntax.apps term args

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

prettyTerm :: Context v -> Syntax.Term v -> Doc ann
prettyTerm context =
  Pretty.prettyTerm 0 (Context.toPrettyEnvironment context)

prettyValue :: Context v -> Domain.Value -> M (Doc ann)
prettyValue context value = do
  term <- readback context value
  pure $ prettyTerm context term
