{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language ViewPatterns #-}
module Elaboration where

import Protolude hiding (Seq, force, check, evaluate, until)

import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef
import Data.Text.Prettyprint.Doc (Doc)
import Rock

import Binding (Binding)
import qualified Binding
import qualified Builtin
import Context (Context)
import qualified Substitution
import qualified Context
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Elaboration.Clauses as Clauses
import qualified Elaboration.Matching as Matching
import Elaboration.Matching.SuggestedName as SuggestedName
import qualified Elaboration.Metas as Metas
import qualified Environment
import Error (Error)
import qualified Error
import qualified Error.Hydrated as Error
import qualified Evaluation
import qualified Flexibility
import Index
import qualified Inlining
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Presyntax
import qualified "this" Data.IntMap as IntMap
import qualified Query
import qualified Readback
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified Unification
import Var (Var)

inferTopLevelDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> M ((Syntax.Definition, Syntax.Type Void, Meta.Vars (Syntax.Term Void)), [Error])
inferTopLevelDefinition key def = do
  context <- Context.empty key
  (def', typeValue) <- inferDefinition context def
  type_ <- readback context typeValue
  metaVars <- liftIO $ readIORef $ Context.metas context
  errors <- liftIO $ readIORef $ Context.errors context
  pure ((def', type_, metaVars), toList errors)

checkTopLevelDefinition
  :: Scope.KeyedName
  -> Presyntax.Definition
  -> Domain.Type
  -> M ((Syntax.Definition, Meta.Vars (Syntax.Term Void)), [Error])
checkTopLevelDefinition key def type_ = do
  context <- Context.empty key
  def' <- checkDefinition context def type_
  metaVars <- liftIO $ readIORef $ Context.metas context
  errors <- liftIO $ readIORef $ Context.errors context
  pure ((def', metaVars), toList errors)

checkDefinitionMetaSolutions
  :: Scope.KeyedName
  -> Syntax.Definition
  -> Syntax.Type Void
  -> Meta.Vars (Syntax.Term Void)
  -> M ((Syntax.Definition, Syntax.Type Void), [Error])
checkDefinitionMetaSolutions key def type_ metas = do
  context <- Context.empty key
  metasVar <- liftIO $ newIORef metas
  let
    context' = context { Context.metas = metasVar }
  metas' <- checkMetaSolutions context' metas
  (def', type') <- Metas.inlineSolutions key metas' def type_
  def'' <- Inlining.inlineDefinition key def'
  type'' <- Inlining.inlineTerm (Environment.empty key) type'
  errors <- liftIO $ readIORef $ Context.errors context'
  pure ((def'', type''), toList errors)

checkDefinition
  :: Context Void
  -> Presyntax.Definition
  -> Domain.Type
  -> M Syntax.Definition
checkDefinition context def expectedType =
  case def of
    Presyntax.TypeDeclaration _ type_ -> do
      type' <- check context type_ expectedType
      pure $ Syntax.TypeDeclaration type'

    Presyntax.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | (_, clause) <- clauses]
      term' <- Clauses.check context clauses' expectedType
      pure $ Syntax.ConstantDefinition term'

    Presyntax.DataDefinition span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context span params constrs mempty
      type' <- evaluate context type_
      success <- Context.try_ context $ Unification.unify context Flexibility.Rigid type' expectedType
      if success then
        pure $ Syntax.DataDefinition boxity tele

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
    Presyntax.TypeDeclaration _ type_ -> do
      type' <- check context type_ Builtin.Type
      pure (Syntax.TypeDeclaration type', Builtin.Type)

    Presyntax.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | (_, clause) <- clauses]
      (term', type_) <- Clauses.infer context clauses'
      pure (Syntax.ConstantDefinition term', type_)

    Presyntax.DataDefinition span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context span params constrs mempty
      type' <- evaluate context type_
      pure (Syntax.DataDefinition boxity tele, type')

-------------------------------------------------------------------------------

inferDataDefinition
  :: Context v
  -> Span.Relative
  -> [(Presyntax.Binding, Presyntax.Type, Plicity)]
  -> [Presyntax.ConstructorDefinition]
  -> Tsil (Plicity, Var)
  -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v, Syntax.Type v)
inferDataDefinition context thisSpan preParams constrs paramVars =
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
            (Environment.empty $ Context.scopeKey context)
            (toList paramVars)
            Builtin.Type

      thisType' <- evaluate context thisType

      let
        thisBinding =
          Binding.Spanned $ pure (thisSpan, thisName)

      (context', var) <-
        Context.extend context thisBinding thisType'

      lazyReturnType <-
        lazy $
          readback context' $
          Domain.Neutral (Domain.Global qualifiedThisName) $
          second Domain.var <$> paramVars

      constrs' <- forM constrs $ \case
        Presyntax.GADTConstructors cs type_ -> do
          type' <- checkConstructorType context' type_ var paramVars
          type'' <- Substitution.let_ context this type'
          pure [(constr, type'') | (_, constr) <- cs]

        Presyntax.ADTConstructor _ constr types -> do
          types' <- forM types $ \type_ ->
            check context' type_ Builtin.Type

          returnType <- force lazyReturnType
          let
            type_ =
              Syntax.funs types' Explicit returnType
          type' <- Substitution.let_ context this type_
          pure [(constr, type')]
      pure
        ( Telescope.Empty (Syntax.ConstructorDefinitions $ HashMap.fromList $ concat constrs')
        , Syntax.Global Builtin.TypeName
        )

    (binding, type_, plicity):preParams' -> do
      type' <- check context type_ Builtin.Type
      type'' <- evaluate context type'
      (context', paramVar) <- Context.extend context (Binding.fromPresyntax binding) type''
      let
        paramVars' =
          paramVars Tsil.:> (plicity, paramVar)

        binding' =
          Binding.fromPresyntax binding
      (tele, dataType) <- inferDataDefinition context' thisSpan preParams' constrs paramVars'
      pure
        ( Telescope.Extend binding' type' plicity tele
        , Syntax.Pi binding' type' plicity dataType
        )

varPis
  :: Context v
  -> Domain.Environment v'
  -> [(Plicity, Var)]
  -> Domain.Value
  -> M (Syntax.Term v')
varPis context env vars target =
  case vars of
    [] ->
      Readback.readback env target

    (plicity, var):vars'-> do
      let
        env' =
          Environment.extendVar env var

        domain =
          Context.lookupVarType var context
      domain' <- Readback.readback env domain
      target' <- varPis context env' vars' target
      let
        binding =
          Binding.Unspanned $ Context.lookupVarName var context

      pure $ Syntax.Pi binding domain' plicity target'

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
  constrType <- check context' term Builtin.Type
  maybeConstrType'' <- Context.try context' $ goTerm context' constrType
  pure $
    fromMaybe
      (Syntax.App (Syntax.Global Builtin.fail) Explicit Builtin.type_)
      maybeConstrType''
  where
    goTerm :: Context v -> Syntax.Term v -> M (Syntax.Term v)
    goTerm context' constrType = do
      case constrType of
        Syntax.Spanned span' constrType' -> do
          constrType'' <- goTerm (Context.spanned span' context') constrType'
          pure $ Syntax.Spanned span' constrType''

        Syntax.Pi binding domain plicity target -> do
          domain' <- evaluate context' domain
          (context'', _) <- Context.extendUnnamed context' (Binding.toName binding) domain'
          target' <- goTerm context'' target
          pure $ Syntax.Pi binding domain plicity target'

        Syntax.Fun domain plicity target -> do
          target' <- goTerm context' target
          pure $ Syntax.Fun domain plicity target'

        (Syntax.appsView -> (hd@(Syntax.varView -> Just headIndex), indices))
          | Context.lookupIndexVar headIndex context' == dataVar ->
            termIndexEqualities context' (toList indices) (toList paramVars) hd mempty

        _ -> do
          constrType' <- evaluate context' constrType
          goValue context' constrType'

    goValue :: Context v -> Domain.Value -> M (Syntax.Term v)
    goValue context' constrType = do
      constrType' <- Context.forceHead context constrType
      case constrType' of
        Domain.Pi name domain plicity targetClosure -> do
          domain' <- readback context' domain
          (context'', var) <- Context.extendUnnamed context' name domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          target' <- goValue context'' target
          pure $ Syntax.Pi (Binding.Unspanned name) domain' plicity target'

        Domain.Fun domain plicity target -> do
          domain' <- readback context' domain
          target' <- goValue context' target
          pure $ Syntax.Fun domain' plicity target'

        Domain.Neutral (Domain.Var headVar) indices
          | headVar == dataVar ->
            valueIndexEqualities context' (toList indices) (toList paramVars)

        _ -> do
          Unification.unify
            context'
            Flexibility.Rigid
            constrType
            (Domain.Neutral
              (Domain.Var dataVar)
              ((\(plicity, var) -> (plicity, Domain.var var)) <$> paramVars))
          readback context' constrType

    termIndexEqualities
      :: Context v
      -> [(Plicity, Syntax.Term v)]
      -> [(Plicity, Var)]
      -> Syntax.Term v
      -> Tsil (Plicity, Syntax.Term v)
      -> M (Syntax.Term v)
    termIndexEqualities context' indices paramVars' hd params =
      case (indices, paramVars') of
        ((plicity1, index):indices', (plicity2, paramVar):paramVars'')
          | plicity1 == plicity2 -> do
            index' <- evaluate context' index
            index'' <- Context.forceHead context' index'
            case index'' of
              Domain.Neutral (Domain.Var indexVar) Tsil.Empty
                | indexVar == paramVar ->
                  termIndexEqualities context' indices' paramVars'' hd (params Tsil.:> (plicity1, index))

              _ -> do
                paramType <- readback context' $ Context.lookupVarType paramVar context'
                param <- readback context' $ Domain.var paramVar
                let
                  domain =
                    Builtin.equals paramType index param

                target <- termIndexEqualities context' indices' paramVars'' hd (params Tsil.:> (plicity1, param))
                pure $ Syntax.Fun domain Constraint target

          | otherwise ->
            panic "indexEqualities plicity mismatch"

        ([], []) ->
          pure $ Syntax.apps hd params

        _ ->
          panic "indexEqualities length mismatch"

    valueIndexEqualities
      :: Context v
      -> [(Plicity, Domain.Value)]
      -> [(Plicity, Var)]
      -> M (Syntax.Term v)
    valueIndexEqualities context' indices paramVars' =
      case (indices, paramVars') of
        ((plicity1, index):indices', (plicity2, paramVar):paramVars'')
          | plicity1 == plicity2 -> do
            index' <- Context.forceHead context' index
            case index' of
              Domain.Neutral (Domain.Var indexVar) Tsil.Empty
                | indexVar == paramVar ->
                  valueIndexEqualities context' indices' paramVars''

              _ -> do
                let
                  domain =
                    Builtin.Equals
                      (Context.lookupVarType paramVar context')
                      index
                      (Domain.var paramVar)

                domain' <- readback context' domain

                target <- valueIndexEqualities context' indices' paramVars''
                pure $ Syntax.Fun domain' Constraint target

          | otherwise ->
            panic "indexEqualities plicity mismatch"

        ([], []) ->
          readback context' $
            Domain.Neutral (Domain.Var dataVar) $
            second Domain.var <$> paramVars

        _ ->
          panic "indexEqualities length mismatch"

-------------------------------------------------------------------------------

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context (Presyntax.Term span term) type_ =
  -- traceShow ("check", term) $
  Syntax.Spanned span <$> checkUnspanned (Context.spanned span context) term type_

-- check context (Presyntax.Term span term) type_ = do
--   putText $ "check "  <> show term
--   result <- checkUnspanned (Context.spanned span context) term type_
--   prettyType <- prettyValue context type_
--   prettyResult <- prettyTerm context result
--   putText ""
--   putText "check"
--   putText $ "    " <> show term
--   putText $ "    " <> show prettyType
--   putText $ "  = " <> show prettyResult
--   pure result

infer
  :: Context v
  -> Presyntax.Term
  -> M (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
infer context (Presyntax.Term span term) expectedTypeName =
  -- traceShow ("infer", term) $
  first (Syntax.Spanned span) <$> inferUnspanned (Context.spanned span context) term expectedTypeName

-- infer context (Presyntax.Term span term) expectedTypeName = do
--   putText $ "infer "  <> show term
--   (term', type_) <- inferUnspanned (Context.spanned span context) term expectedTypeName
--   prettyType <- prettyValue context type_
--   prettyResult <- prettyTerm context term'
--   putText ""
--   putText "infer"
--   putText $ "    " <> show term
--   putText $ "  = " <> show prettyResult
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
    (Presyntax.Let name maybeType clauses body, _) -> do
      (context', binding, boundTerm, typeTerm) <- elaborateLet context name maybeType clauses
      body' <- check context' body expectedType
      pure $ Syntax.Let binding boundTerm typeTerm body'

    (Presyntax.Case scrutinee branches, _) -> do
      (scrutinee', scrutineeType) <-
        inferAndInsertMetas context UntilExplicit scrutinee $ pure Nothing
      Matching.elaborateCase context scrutinee' scrutineeType branches expectedType

    (Presyntax.Lam (Presyntax.ExplicitPattern pat) body, Domain.Pi name domain Explicit targetClosure) ->
      checkLambda context name domain Explicit pat targetClosure body

    (Presyntax.Lam (Presyntax.ExplicitPattern pat) body, Domain.Fun domain Explicit target) -> do
      domain' <- readback context domain
      binding <- SuggestedName.patternBinding context pat "x"
      (context', var) <- Context.extendUnnamed context (Binding.toName binding) domain
      body' <- Matching.elaborateSingle context' var Explicit pat body target
      pure $ Syntax.Lam binding domain' Explicit body'

    (Presyntax.Lam (Presyntax.ImplicitPattern _ namedPats) body, _)
      | HashMap.null namedPats ->
        check context body expectedType

    (Presyntax.Lam (Presyntax.ImplicitPattern span namedPats) body, Domain.Pi name domain Implicit targetClosure)
      | name `HashMap.member` namedPats -> do
        let
          pat =
            namedPats HashMap.! name

          body' =
            Presyntax.Term (Context.span context) $
              Presyntax.Lam (Presyntax.ImplicitPattern span (HashMap.delete name namedPats)) body
        checkLambda context name domain Implicit pat targetClosure body'

    (_, Domain.Pi name domain Implicit targetClosure) -> do
      (context', v) <- Context.extendUnnamed context name domain
      target <- Evaluation.evaluateClosure targetClosure $ Domain.var v
      domain' <- readback context domain
      term' <- checkUnspanned context' term target
      pure $ Syntax.Lam (Binding.Unspanned name) domain' Implicit term'

    (Presyntax.App function argument, _) -> do
      let
        expectedTypeName =
          getExpectedTypeName context expectedType'
      (function', functionType) <-
        inferAndInsertMetas context UntilExplicit function expectedTypeName
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ domain Explicit targetClosure -> do
          (argument', target) <- checkApplication context argument domain targetClosure
          f <- subtype context target expectedType
          pure $ f $ Syntax.App function' Explicit argument'

        Domain.Fun domain Explicit target -> do
          f <- subtype context target expectedType
          argument' <- check context argument domain
          pure $ f $ Syntax.App function' Explicit argument'

        _ -> do
          domain <- Context.newMetaType context
          target <- Context.newMetaType context
          let
            metaFunctionType =
              Domain.Fun domain Explicit expectedType
          f <- Unification.tryUnify context functionType metaFunctionType
          g <- subtype context target expectedType
          argument' <- check context argument domain
          pure $ g $ Syntax.App (f function') Explicit argument'

    (Presyntax.ImplicitApps function arguments, _)
      | HashMap.null arguments ->
        check context function expectedType

    (Presyntax.Wildcard, _) -> do
      term' <- Context.newMeta expectedType context
      readback context term'

    (Presyntax.ParseError err, _) -> do
      Context.reportParseError context err
      checkUnspanned context Presyntax.Wildcard expectedType

    _ -> do
      let
        expectedTypeName =
          getExpectedTypeName context expectedType'
      (term', type_) <- inferUnspanned context term expectedTypeName
      f <- subtype context type_ expectedType
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

    Presyntax.Let name maybeType clauses body -> do
      (context', binding, boundTerm, typeTerm) <- elaborateLet context name maybeType clauses
      (body', type_) <- infer context' body expectedTypeName
      pure (Syntax.Let binding boundTerm typeTerm body', type_)

    Presyntax.Pi binding plicity domain target -> do
      domain' <- check context domain Builtin.Type
      domain'' <- evaluate context domain'

      (context', _) <- Context.extend context (Binding.fromPresyntax binding) domain''

      target' <- check context' target Builtin.Type
      pure
        ( Syntax.Pi (Binding.fromPresyntax binding) domain' plicity target'
        , Builtin.Type
        )

    Presyntax.Fun domain target -> do
      domain' <- check context domain Builtin.Type
      target' <- check context target Builtin.Type
      pure
        ( Syntax.Fun domain' Explicit target'
        , Builtin.Type
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
        inferAndInsertMetas context UntilExplicit function expectedTypeName
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ domain Explicit targetClosure -> do
          (argument', target) <- checkApplication context argument domain targetClosure
          pure
            ( Syntax.App function' Explicit argument'
            , target
            )

        Domain.Fun domain Explicit target -> do
          argument' <- check context argument domain
          pure
            ( Syntax.App function' Explicit argument'
            , target
            )

        _ -> do
          domain <- Context.newMetaType context
          target <- Context.newMetaType context
          let
            metaFunctionType =
              Domain.Fun domain Explicit target

          f <- Unification.tryUnify context functionType metaFunctionType
          argument' <- check context argument domain
          pure
            ( Syntax.App (f function') Explicit argument'
            , target
            )

    Presyntax.ImplicitApps function arguments -> do
      (function', functionType) <-
        inferAndInsertMetas context (UntilImplicit (`HashMap.member` arguments)) function expectedTypeName
      go function' arguments functionType

      where
        go function' arguments' functionType
          | HashMap.null arguments' =
            pure (function', functionType)

          | otherwise = do
            (metaArgs, functionType') <-
              insertMetasReturningSyntax context (UntilImplicit (`HashMap.member` arguments')) functionType

            let
              function'' =
                Syntax.apps function' metaArgs
            functionType'' <- Context.forceHead context functionType'
            case functionType'' of
              Domain.Pi name domain Implicit targetClosure
                | name `HashMap.member` arguments' -> do
                  argument' <- check context (arguments' HashMap.! name) domain
                  argument'' <- evaluate context argument'
                  target <- Evaluation.evaluateClosure targetClosure argument''
                  go
                    (Syntax.App function'' Implicit argument')
                    (HashMap.delete name arguments')
                    target
              _
                | [(name, argument)] <- HashMap.toList arguments' -> do
                  domain <- Context.newMetaType context
                  target <- Context.newMetaType context
                  (context', _) <- Context.extendUnnamed context name domain
                  target' <- readback context' target
                  let
                    metaFunctionType =
                      Domain.Pi name domain Implicit $
                      Domain.Closure (Context.toEnvironment context) target'
                  f <- Unification.tryUnify context functionType' metaFunctionType
                  argument' <- check context argument domain
                  pure (Syntax.App (f function'') Implicit argument', target)

              _ -> do
                functionType''' <- readback context functionType'
                pfunction <- Context.toPrettyableTerm context function''
                pfunctionType <- Context.toPrettyableTerm context functionType'''
                Context.report context $
                  Error.ImplicitApplicationMismatch
                    (HashSet.fromMap $ void arguments')
                    pfunction
                    pfunctionType
                inferenceFailed context

    Presyntax.Case scrutinee branches -> do
      (scrutinee', scrutineeType) <-
        inferAndInsertMetas context UntilExplicit scrutinee $ pure Nothing
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
      let
        type_ =
          Context.lookupVarType var context
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
          maybeConstr <- resolveConstructor candidates expectedTypeName
          case maybeConstr of
            Ambiguous candidates' -> do
              Context.report context $ Error.Ambiguous name candidates' mempty
              inferenceFailed context

            Resolved constr -> do
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
  -> Domain.Type
  -> Plicity
  -> Presyntax.Pattern
  -> Domain.Closure
  -> Presyntax.Term
  -> M (Syntax.Term v)
checkLambda context name domain plicity pat targetClosure body = do
  (context', var) <- Context.extendUnnamed context name domain
  domain' <- readback context domain
  target <-
    Evaluation.evaluateClosure
      targetClosure
      (Domain.var var)
  body' <- Matching.elaborateSingle context' var plicity pat body target
  binding <- SuggestedName.patternBinding context pat name
  pure $ Syntax.Lam binding domain' plicity body'

inferLambda
  :: Context v
  -> Name
  -> Plicity
  -> Presyntax.Pattern
  -> Presyntax.Term
  -> M (Syntax.Term v, Domain.Type)
inferLambda context name plicity pat body = do
  domain <- Context.newMetaType context
  domain' <- readback context domain
  (context', var) <- Context.extendUnnamed context name domain
  target <- Context.newMetaType context'
  body' <- Matching.elaborateSingle context' var plicity pat body target
  target' <- readback context' target
  binding <- SuggestedName.patternBinding context pat name
  pure
    ( Syntax.Lam binding domain' plicity body'
    , Domain.Pi name domain plicity
      $ Domain.Closure (Context.toEnvironment context) target'
    )

checkApplication
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> Domain.Closure
  -> M (Syntax.Term v, Domain.Value)
checkApplication context argument domain targetClosure = do
  argument' <- check context argument domain
  argument'' <- evaluate context argument'
  target <- Evaluation.evaluateClosure targetClosure argument''
  pure (argument', target)

elaborateLet
  :: Context v
  -> Name
  -> Maybe (Span.Relative, Presyntax.Type)
  -> [(Span.Relative, Presyntax.Clause)]
  -> M (Context (Succ v), Binding, Syntax.Term v, Syntax.Type v)
elaborateLet context name maybeType clauses = do
  let
    clauses' =
      [ Clauses.Clause clause mempty | (_, clause) <- clauses]
  (binding, boundTerm, typeTerm, typeValue) <-
    case maybeType of
      Nothing -> do
        (boundTerm, typeValue) <- Clauses.infer context clauses'
        typeTerm <- readback context typeValue
        pure (Binding.fromName (map fst clauses) name, boundTerm, typeTerm, typeValue)

      Just (span, type_) -> do
        typeTerm <- check context type_ Builtin.Type
        typeValue <- evaluate context typeTerm
        boundTerm <- Clauses.check context clauses' typeValue
        pure (Binding.fromName (span : map fst clauses) name, boundTerm, typeTerm, typeValue)

  boundTerm' <- evaluate context boundTerm
  (context', _) <- Context.extendDef context binding boundTerm' typeValue
  pure (context', binding, boundTerm, typeTerm)

data ResolvedConstructor
  = Ambiguous (HashSet Name.QualifiedConstructor)
  | Resolved !Name.QualifiedConstructor
  deriving Show

resolveConstructor
  :: HashSet Name.QualifiedConstructor
  -> M (Maybe Name.Qualified)
  -> M ResolvedConstructor
resolveConstructor candidates expectedTypeName =
  case toList candidates of
    [constr] ->
      pure $ Resolved constr

    _ -> do
      maybeExpectedTypeName <- expectedTypeName
      case maybeExpectedTypeName of
        Nothing ->
          pure $ Ambiguous candidates

        Just typeName -> do
          let
            constrs' =
              HashSet.filter
                (\(Name.QualifiedConstructor constrTypeName _) -> constrTypeName == typeName)
                candidates
          case toList constrs' of
            [constr] ->
              pure $ Resolved constr

            _ ->
              pure $ Ambiguous constrs'

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

    Domain.Glued _ _ value -> do
      value' <- force value
      getExpectedTypeName context value'

    Domain.Pi name domain _ targetClosure -> do
      (context', var) <- Context.extendUnnamed context name domain
      target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
      getExpectedTypeName context' target

    Domain.Fun _ _ target ->
      getExpectedTypeName context target

    Domain.Lam {} ->
      pure Nothing

    Domain.Case {} ->
      pure Nothing

-------------------------------------------------------------------------------
-- Implicits

data InsertUntil
  = UntilTheEnd
  | UntilExplicit
  | UntilImplicit (Name -> Bool)

inferAndInsertMetas
  :: Context v
  -> InsertUntil
  -> Presyntax.Term
  -> M (Maybe Name.Qualified)
  -> M (Syntax.Term v, Domain.Type)
inferAndInsertMetas context until (Presyntax.Term span term) expectedTypeName = do
  (term', type_) <- inferUnspanned (Context.spanned span context) term expectedTypeName
  (args, type') <- insertMetasReturningSyntax context until type_
  pure (Syntax.Spanned span $ Syntax.apps term' args, type')

insertMetasReturningSyntax
  :: Context v
  -> InsertUntil
  -> Domain.Type
  -> M ([(Plicity, Syntax.Term v)], Domain.Type)
insertMetasReturningSyntax context until type_ = do
  (args, res) <- insertMetas context until type_
  args' <- forM args $ \(plicity, arg) -> do
    arg' <- readback context arg
    pure (plicity, arg')
  pure (args', res)

insertMetas
  :: Context v
  -> InsertUntil
  -> Domain.Type
  -> M ([(Plicity, Domain.Value)], Domain.Type)
insertMetas context until type_ = do
  type' <- Context.forceHead context type_
  case (until, type') of
    (UntilTheEnd, Domain.Pi _ domain plicity targetClosure) ->
      instantiate domain plicity targetClosure

    (UntilTheEnd, Domain.Fun domain plicity target) -> do
      meta <- Context.newMeta domain context
      (args, res) <- insertMetas context until target
      pure ((plicity, meta) : args, res)

    (UntilExplicit, Domain.Pi _ domain Implicit targetClosure) ->
      instantiate domain Implicit targetClosure

    (UntilImplicit stopAt, Domain.Pi name domain Implicit targetClosure)
      | not $ stopAt name ->
        instantiate domain Implicit targetClosure

    (_, Domain.Pi _ domain Constraint targetClosure) -> do
      domain' <- Context.forceHead context domain
      case domain' of
        Builtin.Equals kind term1 term2 -> do
          f <- Unification.tryUnifyD context term1 term2
          let
            value =
              Builtin.Refl kind term1 term2
          target <- Evaluation.evaluateClosure targetClosure value
          (args, res) <- insertMetas context until target
          pure ((Constraint, f value) : args, res)

        _ ->
          panic "insertMetas: non-equality constraint"

    (_, Domain.Fun domain Constraint target) -> do
      domain' <- Context.forceHead context domain
      case domain' of
        Builtin.Equals kind term1 term2 -> do
          f <- Unification.tryUnifyD context term1 term2
          let
            value =
              Builtin.Refl kind term1 term2
          (args, res) <- insertMetas context until target
          pure ((Constraint, f value) : args, res)

        _ ->
          panic "insertMetas: non-equality constraint"

    _ ->
      pure ([], type_)
  where
    instantiate domain plicity targetClosure = do
      meta <- Context.newMeta domain context
      target <- Evaluation.evaluateClosure targetClosure meta
      (args, res) <- insertMetas context until target
      pure ((plicity, meta) : args, res)

subtype
  :: Context v
  -> Domain.Type
  -> Domain.Type
  -> M (Syntax.Term v -> Syntax.Term v)
subtype context type1 type2 = do
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

  (args, type1') <- insertMetasReturningSyntax context until type1
  f <- Unification.tryUnify context type1' type2
  pure $ \term -> f $ Syntax.apps term args

subtypeWithoutRecovery
  :: Context v
  -> Domain.Type
  -> Domain.Type
  -> M (Syntax.Term v -> Syntax.Term v)
subtypeWithoutRecovery context type1 type2 = do
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

  (args, type1') <- insertMetasReturningSyntax context until type1
  Unification.unify context Flexibility.Rigid type1' type2
  pure $ \term -> Syntax.apps term args

-------------------------------------------------------------------------------
-- Meta solutions

checkMetaSolutions
  :: Context Void
  -> Meta.Vars (Syntax.Term Void)
  -> M Syntax.MetaSolutions
checkMetaSolutions context metaVars = do
  flip IntMap.traverseWithKey (Meta.vars metaVars) $ \index var ->
    case var of
      Meta.Unsolved type_ span -> do
        ptype <- Context.toPrettyableClosedTerm context type_
        Context.report (Context.spanned span context) $
          Error.UnsolvedMetaVariable index ptype
        type' <- evaluate (Context.emptyFrom context) type_
        failTerm <- addLambdas (Context.emptyFrom context) type'
        pure (failTerm, type_)

      Meta.Solved solution type_ ->
        pure (solution, type_)
  where
    addLambdas :: Context v -> Domain.Type -> M (Syntax.Term v)
    addLambdas context' type_ = do
      type' <- Context.forceHead context' type_
      case type' of
        Domain.Fun domain Explicit target -> do
          domain' <- readback context' domain
          (context'', _) <- Context.extendUnnamed context' "x" domain
          body <- addLambdas context'' target
          pure $ Syntax.Lam "x" domain' Explicit body

        Domain.Pi name domain Explicit targetClosure -> do
          domain' <- readback context' domain
          (context'', var) <- Context.extendUnnamed context' name domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          body <- addLambdas context'' target
          pure $ Syntax.Lam (Binding.Unspanned name) domain' Explicit body

        _ -> do
          typeTerm <- readback context' type_
          pure $ Syntax.App (Syntax.Global Builtin.fail) Explicit typeTerm

-------------------------------------------------------------------------------

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEnvironment context)

readback :: Context v -> Domain.Value -> M (Syntax.Term v)
readback context =
  Readback.readback (Context.toEnvironment context)

prettyTerm :: Context v -> Syntax.Term v -> M (Doc ann)
prettyTerm context term = do
  pterm <- Context.toPrettyableTerm context term
  Error.prettyPrettyableTerm 0 pterm

prettyValue :: Context v -> Domain.Value -> M (Doc ann)
prettyValue context value = do
  term <- readback context value
  prettyTerm context term
