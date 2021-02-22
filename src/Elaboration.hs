{-# language DeriveFunctor #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language ViewPatterns #-}
module Elaboration where

import Protolude hiding (IntMap, Seq, force, check, evaluate, until)

import Data.Coerce
import Data.Functor.Compose
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef.Lifted
import Data.Text.Prettyprint.Doc (Doc)
import Rock

import Boxity
import qualified Builtin
import Core.Binding (Binding)
import qualified Core.Binding as Binding
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import qualified Data.IntMap as IntMap
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Elaboration.Clauses as Clauses
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Elaboration.Matching as Matching
import Elaboration.Matching.SuggestedName as SuggestedName
import qualified Elaboration.Meta as Meta
import qualified Elaboration.MetaInlining as MetaInlining
import qualified Elaboration.Postponed as Postponed
import qualified Elaboration.Substitution as Substitution
import qualified Elaboration.Unification as Unification
import qualified Elaboration.ZonkPostponedChecks as ZonkPostponedChecks
import qualified Environment
import Error (Error)
import qualified Error
import qualified Error.Hydrated as Error
import qualified Flexibility
import qualified Index
import qualified Inlining
import Literal (Literal)
import qualified Literal
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Postponement
import qualified Query
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

inferTopLevelDefinition
  :: Scope.KeyedName
  -> Surface.Definition
  -> M ((Syntax.Definition, Syntax.Type Void, Meta.Vars), [Error])
inferTopLevelDefinition key def = do
  context <- Context.empty key
  (def', typeValue) <- inferDefinition context def
  type_ <- readback context typeValue
  postponed <- readIORef $ Context.postponed context
  metaVars <- readIORef $ Context.metas context
  errors <- readIORef $ Context.errors context
  pure ((ZonkPostponedChecks.zonkDefinition postponed def', type_, metaVars), toList errors)

checkTopLevelDefinition
  :: Scope.KeyedName
  -> Surface.Definition
  -> Domain.Type
  -> M ((Syntax.Definition, Meta.Vars), [Error])
checkTopLevelDefinition key def type_ = do
  context <- Context.empty key
  def' <- checkDefinition context def type_
  postponed <- readIORef $ Context.postponed context
  metaVars <- readIORef $ Context.metas context
  errors <- readIORef $ Context.errors context
  pure ((ZonkPostponedChecks.zonkDefinition postponed def', metaVars), toList errors)

checkDefinitionMetaSolutions
  :: Scope.KeyedName
  -> Syntax.Definition
  -> Syntax.Type Void
  -> Meta.Vars
  -> M ((Syntax.Definition, Syntax.Type Void), [Error])
checkDefinitionMetaSolutions key def type_ metas = do
  context <- Context.empty key
  metasVar <- newIORef metas
  let
    context' = context { Context.metas = metasVar }
  metas' <- checkMetaSolutions context' metas
  (def', type') <- MetaInlining.inlineSolutions key metas' def type_
  def'' <- Inlining.inlineDefinition key def'
  type'' <- Inlining.inlineTerm (Environment.empty key) type'
  errors <- readIORef $ Context.errors context'
  pure ((def'', type''), toList errors)

checkDefinition
  :: Context Void
  -> Surface.Definition
  -> Domain.Type
  -> M Syntax.Definition
checkDefinition context def expectedType =
  case def of
    Surface.TypeDeclaration _ type_ -> do
      type' <- check context type_ expectedType
      postProcessDefinition context $ Syntax.TypeDeclaration type'

    Surface.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | (_, clause) <- clauses]
      term' <- Clauses.check context clauses' expectedType
      postProcessDefinition context $ Syntax.ConstantDefinition term'

    Surface.DataDefinition span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context span params constrs mempty
      type' <- evaluate context type_
      success <- Context.try_ context $ Unification.unify context Flexibility.Rigid type' expectedType
      if success then
        postProcessDataDefinition context boxity tele

      else do
        expectedType' <- readback context expectedType
        postProcessDefinition context $
          Syntax.ConstantDefinition $
          Syntax.App (Syntax.Global Builtin.fail) Explicit expectedType'

inferDefinition
  :: Context Void
  -> Surface.Definition
  -> M (Syntax.Definition, Domain.Type)
inferDefinition context def =
  case def of
    Surface.TypeDeclaration _ type_ -> do
      type' <- check context type_ Builtin.Type
      def' <- postProcessDefinition context $ Syntax.TypeDeclaration type'
      pure (def', Builtin.Type)

    Surface.ConstantDefinition clauses -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | (_, clause) <- clauses]
      (term', type_) <- Clauses.infer context clauses'
      def' <- postProcessDefinition context $ Syntax.ConstantDefinition term'
      pure (def', type_)

    Surface.DataDefinition span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context span params constrs mempty
      type' <- evaluate context type_
      def' <- postProcessDataDefinition context boxity tele
      pure (def', type')

postProcessDefinition :: Context v -> Syntax.Definition -> M Syntax.Definition
postProcessDefinition context def = do
  Context.inferAllPostponedChecks context
  postponed <- readIORef $ Context.postponed context
  pure $ ZonkPostponedChecks.zonkDefinition postponed def

-------------------------------------------------------------------------------

inferDataDefinition
  :: Context v
  -> Span.Relative
  -> [(Surface.SpannedName, Surface.Type, Plicity)]
  -> [Surface.ConstructorDefinition]
  -> Tsil (Plicity, Var)
  -> M (Telescope Binding Syntax.Type (Compose Syntax.ConstructorDefinitions Index.Succ) v, Syntax.Type v)
inferDataDefinition context thisSpan preParams constrs paramVars =
  case preParams of
    [] -> do
      let
        Scope.KeyedName _ qualifiedThisName@(Name.Qualified _ thisName) =
          Context.scopeKey context

      thisType <-
        Syntax.fromVoid <$>
          varPis
            context
            (Environment.empty $ Context.scopeKey context)
            (toList paramVars)
            Builtin.Type

      thisType' <- evaluate context thisType

      (context', _) <-
        Context.extendSurface context (Surface.SpannedName thisSpan thisName) thisType'

      constrs' <- forM constrs $ \case
        Surface.GADTConstructors cs type_ -> do
          type' <- check context' type_ Builtin.Type
          pure [(constr, type') | (_, constr) <- cs]

        Surface.ADTConstructor _ constr types -> do
          types' <- forM types $ \type_ ->
            check context' type_ Builtin.Type

          returnType <-
            readback context' $
              Domain.Neutral (Domain.Global qualifiedThisName) $
              Domain.Apps $ second Domain.var <$> paramVars
          let
            type_ =
              Syntax.funs types' Explicit returnType
          pure [(constr, type_)]
      pure
        ( Telescope.Empty (Compose $ Syntax.ConstructorDefinitions $ OrderedHashMap.fromList $ concat constrs')
        , Syntax.Global Builtin.TypeName
        )

    (binding, type_, plicity):preParams' -> do
      type' <- check context type_ Builtin.Type
      type'' <- evaluate context type'
      (context', paramVar) <- Context.extendSurface context binding type''
      let
        paramVars' =
          paramVars Tsil.:> (plicity, paramVar)

        binding' =
          Binding.fromSurface binding
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

postProcessDataDefinition
   :: Context Void
   -> Boxity.Boxity
   -> Telescope Binding Syntax.Type (Compose Syntax.ConstructorDefinitions Index.Succ) Void
   -> M Syntax.Definition
postProcessDataDefinition outerContext boxity outerTele = do
  Context.inferAllPostponedChecks outerContext
  postponed <- readIORef $ Context.postponed outerContext
  Syntax.DataDefinition boxity <$> go outerContext postponed outerTele mempty
  where
    go
      :: Context v
      -> Postponed.Checks
      -> Telescope Binding Syntax.Type (Compose Syntax.ConstructorDefinitions Index.Succ) v
      -> Tsil (Plicity, Var)
      -> M (Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v)
    go context postponed tele paramVars =
      case tele of
        Telescope.Empty (Compose (Syntax.ConstructorDefinitions constructorDefinitions)) -> do
          let
            Scope.KeyedName _ qualifiedThisName =
              Context.scopeKey context

            this =
              Syntax.Global qualifiedThisName

          map (Telescope.Empty . Syntax.ConstructorDefinitions) $ OrderedHashMap.forMUnordered constructorDefinitions $ \constructorType -> do
            let
              zonkedConstructorType =
                ZonkPostponedChecks.zonkTerm postponed constructorType
            constructorType' <- Substitution.let_ context this zonkedConstructorType
            maybeConstructorType <- Context.try context $ addConstructorIndexEqualities context paramVars constructorType'
            pure $
              fromMaybe
                (Syntax.App (Syntax.Global Builtin.fail) Explicit Builtin.type_)
                maybeConstructorType

        Telescope.Extend name type_ plicity tele' -> do
          typeValue <- evaluate context type_
          (context', paramVar) <- Context.extend context (Binding.toName name) typeValue
          let
            zonkedType =
              ZonkPostponedChecks.zonkTerm postponed type_
          Telescope.Extend name zonkedType plicity <$> go context' postponed tele' (paramVars Tsil.:> (plicity, paramVar))


addConstructorIndexEqualities :: Context v -> Tsil (Plicity, Var) -> Syntax.Term v -> M (Syntax.Term v)
addConstructorIndexEqualities context paramVars constrType =
  case constrType of
    Syntax.Spanned span' constrType' -> do
      constrType'' <- addConstructorIndexEqualities (Context.spanned span' context) paramVars constrType'
      pure $ Syntax.Spanned span' constrType''

    Syntax.Pi binding domain plicity target -> do
      domain' <- evaluate context domain
      (context'', _) <- Context.extend context (Binding.toName binding) domain'
      target' <- addConstructorIndexEqualities context'' paramVars target
      pure $ Syntax.Pi binding domain plicity target'

    Syntax.Fun domain plicity target -> do
      target' <- addConstructorIndexEqualities context paramVars target
      pure $ Syntax.Fun domain plicity target'

    (Syntax.appsView -> (hd@(Syntax.globalView -> Just headGlobal), indices))
      | headGlobal == dataName ->
        termIndexEqualities context (toList indices) (toList paramVars) hd mempty

    _ -> do
      constrType' <- evaluate context constrType
      goValue context constrType'

  where
    Scope.KeyedName _ dataName =
      Context.scopeKey context

    goValue :: Context v -> Domain.Value -> M (Syntax.Term v)
    goValue context' constrTypeValue = do
      constrType' <- Context.forceHead context constrTypeValue
      case constrType' of
        Domain.Pi binding domain plicity targetClosure -> do
          domain' <- readback context' domain
          (context'', var) <- Context.extend context' (Binding.toName binding) domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          target' <- goValue context'' target
          pure $ Syntax.Pi binding domain' plicity target'

        Domain.Fun domain plicity target -> do
          domain' <- readback context' domain
          target' <- goValue context' target
          pure $ Syntax.Fun domain' plicity target'

        Domain.Neutral (Domain.Global headGlobal) (Domain.appsView -> Just indices)
          | headGlobal == dataName ->
            valueIndexEqualities context' (toList indices) (toList paramVars)

        _ -> do
          f <- Unification.tryUnify
            context'
            constrTypeValue
            (Domain.Neutral
              (Domain.Global dataName)
              (Domain.Apps $ second Domain.var <$> paramVars))
          f <$> readback context' constrTypeValue

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
              Domain.Neutral (Domain.Var indexVar) Domain.Empty
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
              Domain.Neutral (Domain.Var indexVar) Domain.Empty
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
            Domain.Neutral (Domain.Global dataName) $
            Domain.Apps $ second Domain.var <$> paramVars

        _ ->
          panic "indexEqualities length mismatch"

-------------------------------------------------------------------------------

check
  :: Context v
  -> Surface.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context term type_ =
  coerce $ elaborate context term $ Check type_

infer
  :: Context v
  -> Surface.Term
  -> M (Maybe (Either Meta.Index Name.Qualified))
  -> M (Inferred (Syntax.Term v))
infer context term expectedTypeName =
  elaborate context term $ Infer expectedTypeName

data Inferred t = Inferred t Domain.Type
  deriving Functor

newtype Checked t = Checked t
  deriving Functor

data Mode result where
  Infer :: M (Maybe (Either Meta.Index Name.Qualified)) -> Mode Inferred
  Check :: Domain.Type -> Mode Checked

result :: Context v -> Mode result -> Syntax.Term v -> Domain.Type -> M (result (Syntax.Term v))
result context mode term type_ =
  case mode of
    Infer _ ->
      pure $ Inferred term type_

    Check expectedType -> do
      (args, type') <- insertMetasReturningSyntax context UntilExplicit type_
      f <- Unification.tryUnify context type' expectedType
      pure $ Checked $ f $ Syntax.apps term args

implicitLambdaResult :: Context v -> Mode result -> Syntax.Term v -> Domain.Type -> M (result (Syntax.Term v))
implicitLambdaResult context mode term type_ =
  case mode of
    Infer _ ->
      pure $ Inferred term type_

    Check expectedType -> do
      (args, type') <- insertMetasReturningSyntax context (UntilImplicit $ const True) type_
      f <- Unification.tryUnify context type' expectedType
      pure $ Checked $ f $ Syntax.apps term args

elaborate :: Functor result => Context v -> Surface.Term -> Mode result -> M (result (Syntax.Term v))
elaborate context (Surface.Term span term) mode =
  fmap (Syntax.Spanned span) <$> elaborateUnspanned (Context.spanned span context) term mode Postponement.CanPostpone

elaborateUnspanned
  :: Functor result
  => Context v
  -> Surface.UnspannedTerm
  -> Mode result
  -> Postponement.CanPostpone
  -> M (result (Syntax.Term v))
elaborateUnspanned context term mode canPostpone = do
  mode' <- forceExpectedTypeHead context mode
  case (term, mode') of
    (Surface.Lam (Surface.ExplicitPattern pat) body, Check (Domain.Pi piBinding domain Explicit targetClosure)) -> do
      let
        name =
          Binding.toName piBinding
      (context', var) <- Context.extend context name domain
      domain' <- readback context domain
      target <- Evaluation.evaluateClosure targetClosure (Domain.var var)
      body' <- Matching.checkSingle context' var Explicit pat body target
      binding <- SuggestedName.patternBinding context pat name
      pure $ Checked $ Syntax.Lam binding domain' Explicit body'

    (Surface.Lam (Surface.ExplicitPattern pat) body, Check (Domain.Fun domain Explicit target)) -> do
      domain' <- readback context domain
      binding <- SuggestedName.patternBinding context pat "x"
      (context', var) <- Context.extend context (Bindings.toName binding) domain
      body' <- Matching.checkSingle context' var Explicit pat body target
      pure $ Checked $ Syntax.Lam binding domain' Explicit body'

    (Surface.Lam (Surface.ImplicitPattern _ namedPats) body, _)
      | HashMap.null namedPats ->
        elaborate context body mode

    (Surface.Lam (Surface.ImplicitPattern span namedPats) body, Check (Domain.Pi piBinding domain Implicit targetClosure))
      | let name = Binding.toName piBinding
      , name `HashMap.member` namedPats -> do
        let
          pat =
            namedPats HashMap.! name

          body' =
            Surface.Term (Context.span context) $
              Surface.Lam (Surface.ImplicitPattern span (HashMap.delete name namedPats)) body

        (context', var) <- Context.extend context name domain
        domain' <- readback context domain
        target <- Evaluation.evaluateClosure targetClosure (Domain.var var)
        body'' <- Matching.checkSingle context' var Implicit pat body' target
        binding <- SuggestedName.patternBinding context pat name
        pure $ Checked $ Syntax.Lam binding domain' Implicit body''

    (_, Check (Domain.Pi binding domain plicity targetClosure))
      | case plicity of
          Explicit -> False
          Implicit -> True
          Constraint -> True
      -> do
        let
          name =
            Binding.toName binding
        (context', var) <- Context.extend context name domain
        target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
        domain' <- readback context domain
        Checked term' <- elaborateUnspanned context' term (Check target) Postponement.CanPostpone
        pure $ Checked $ Syntax.Lam (Bindings.Unspanned name) domain' plicity term'

    (_, Check expectedType@(Domain.Neutral (Domain.Meta blockingMeta) _))
      | Postponement.CanPostpone <- canPostpone ->
        postponeCheck context term expectedType blockingMeta

    (Surface.Lam plicitPattern body@(Surface.Term bodySpan _), _) -> do
      let
        patternSpan =
          Surface.plicitPatternSpan plicitPattern

        elaborateLambda plicity name pat k = do
          domain <- Context.newMetaType $ Context.spanned patternSpan context
          domain' <- readback context domain
          (context', var) <- Context.extend context name domain
          target <- Context.newMetaType $ Context.spanned bodySpan context'
          body' <- Matching.checkSingle context' var plicity pat body target
          target' <- readback context' target
          binding <- SuggestedName.patternBinding context pat name
          k
            context
            mode
            (Syntax.Lam binding domain' plicity body')
            (Domain.Pi (Binding.Unspanned name) domain plicity
              $ Domain.Closure (Context.toEnvironment context) target'
            )

      case (canPostpone, plicitPattern, mode') of
        (Postponement.CanPostpone, _, Infer _) -> do
          postponeInference context term

        (_, Surface.ExplicitPattern pat, _) ->
          elaborateLambda Explicit "x" pat result

        (_, Surface.ImplicitPattern _ (HashMap.toList -> [(name, pat)]), _) -> do
          elaborateLambda Implicit name pat implicitLambdaResult

        (_, Surface.ImplicitPattern _ _, _) -> do
          Context.report (Context.spanned patternSpan context) Error.UnableToInferImplicitLambda
          elaborationFailed context mode

    (Surface.Var name, _) ->
      case Context.lookupNameVar name context of
        Just var -> do
          term' <- readback context (Domain.var var)
          result context mode term' $ Context.lookupVarType var context

        Nothing -> do
          maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) name

          case maybeScopeEntry of
            Nothing -> do
              Context.report context $ Error.NotInScope name
              elaborationFailed context mode

            Just (Scope.Name qualifiedName) -> do
              type_ <- fetch $ Query.ElaboratedType qualifiedName
              type' <- evaluate context $ Syntax.fromVoid type_
              result context mode (Syntax.Global qualifiedName) type'

            Just (Scope.Constructors constructorCandidates dataCandidates) -> do
              resolution <- resolveConstructor constructorCandidates dataCandidates $
                case mode of
                  Check expectedType ->
                    getExpectedTypeName context expectedType

                  Infer m ->
                    m
              case resolution of
                Left blockingMeta ->
                  case (canPostpone, mode) of
                    (Postponement.CanPostpone, Infer _) ->
                      postponeInference context term

                    (Postponement.CanPostpone, Check expectedType) ->
                      postponeCheck context term expectedType blockingMeta

                    (Postponement.Can'tPostpone, _) -> do
                      Context.report context $ Error.Ambiguous name constructorCandidates dataCandidates
                      elaborationFailed context mode

                Right (Ambiguous constrCandidates' dataCandidates') -> do
                  Context.report context $ Error.Ambiguous name constrCandidates' dataCandidates'
                  elaborationFailed context mode

                Right (ResolvedConstructor constr) -> do
                  type_ <- fetch $ Query.ConstructorType constr
                  type' <- evaluate context $ Syntax.fromVoid $ Telescope.fold Syntax.implicitPi type_
                  result context mode (Syntax.Con constr) type'

                Right (ResolvedData data_) -> do
                  type_ <- fetch $ Query.ElaboratedType data_
                  type' <- evaluate context $ Syntax.fromVoid type_
                  result context mode (Syntax.Global data_) type'

            Just (Scope.Ambiguous constrCandidates dataCandidates) -> do
              Context.report context $ Error.Ambiguous name constrCandidates dataCandidates
              elaborationFailed context mode

    (Surface.Lit lit, _) ->
      result context mode (Syntax.Lit lit) (inferLiteral lit)

    (Surface.Let name maybeType clauses body, _) -> do
      let
        clauses' =
          [ Clauses.Clause clause mempty | (_, clause) <- clauses]
      (bindings, boundTerm, typeTerm, typeValue) <-
        case maybeType of
          Nothing -> do
            (boundTerm, typeValue) <- Clauses.infer context clauses'
            typeTerm <- readback context typeValue
            pure (Bindings.fromName (map fst clauses) name, boundTerm, typeTerm, typeValue)

          Just (span, type_) -> do
            typeTerm <- check context type_ Builtin.Type
            typeValue <- evaluate context typeTerm
            boundTerm <- Clauses.check context clauses' typeValue
            pure (Bindings.fromName (span : map fst clauses) name, boundTerm, typeTerm, typeValue)

      boundValue <- evaluate context boundTerm
      (context', _) <- Context.extendSurfaceDef context name boundValue typeValue
      body' <- elaborate context' body mode
      pure $ Syntax.Let bindings boundTerm typeTerm <$> body'

    (Surface.Pi binding plicity domain target, _) -> do
      domain' <- check context domain Builtin.Type
      domain'' <- evaluate context domain'

      (context', _) <- Context.extendSurface context binding domain''

      target' <- check context' target Builtin.Type
      result context mode (Syntax.Pi (Binding.fromSurface binding) domain' plicity target') Builtin.Type

    (Surface.Fun domain target, _) -> do
      domain' <- check context domain Builtin.Type
      target' <- check context target Builtin.Type
      result context mode (Syntax.Fun domain' Explicit target') Builtin.Type

    (Surface.Case scrutinee branches, _) -> do
      (scrutinee', scrutineeType) <- inferAndInsertMetas context UntilExplicit scrutinee $ pure Nothing
      case mode of
        Infer _ -> do
          expectedType <- Context.newMetaType context
          term' <- Matching.checkCase context scrutinee' scrutineeType branches expectedType Postponement.CanPostpone
          pure $ Inferred term' expectedType

        Check expectedType ->
          Checked <$> Matching.checkCase context scrutinee' scrutineeType branches expectedType Postponement.CanPostpone

    (Surface.App function argument@(Surface.Term argumentSpan _), _) -> do
      (function', functionType) <- inferAndInsertMetas context UntilExplicit function $ getModeExpectedTypeName context mode
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ domain Explicit targetClosure -> do
          argument' <- check context argument domain
          argument'' <- evaluate context argument'
          target <- Evaluation.evaluateClosure targetClosure argument''
          result context mode (Syntax.App function' Explicit argument') target

        Domain.Fun domain Explicit target -> do
          argument' <- check context argument domain
          result context mode (Syntax.App function' Explicit argument') target

        _ -> do
          domain <- Context.newMetaType $ Context.spanned argumentSpan context
          (context', _) <- Context.extend context "x" domain
          target <- Context.newMetaType context'
          target' <- readback context' target
          let
            targetClosure =
              Domain.Closure (Context.toEnvironment context) target'
            metaFunctionType =
              Domain.Pi (Binding.Unspanned "x") domain Explicit targetClosure
          f <- Unification.tryUnify context functionType metaFunctionType
          argument' <- check context argument domain
          argumentValue <- evaluate context argument'
          target'' <- Evaluation.evaluateClosure targetClosure argumentValue
          result context mode (Syntax.App (f function') Explicit argument') target''

    (Surface.ImplicitApps function arguments, _) -> do
      Inferred function' functionType <- infer context function $ getModeExpectedTypeName context mode
      (result_, resultType) <- inferImplicitApps context function' functionType arguments Postponement.CanPostpone
      result context mode result_ resultType

    (Surface.Wildcard, Check expectedType) -> do
      term' <- Context.newMeta context expectedType
      Checked <$> readback context term'

    (Surface.Wildcard, Infer _) -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta context type_
      term'' <- readback context term'
      pure $ Inferred term'' type_

    (Surface.ParseError err, _) -> do
      Context.reportParseError context err
      elaborateUnspanned context Surface.Wildcard mode Postponement.CanPostpone

forceExpectedTypeHead :: Context v -> Mode result -> M (Mode result)
forceExpectedTypeHead context mode =
  case mode of
    Infer _ ->
      pure mode

    Check type_ ->
      Check <$> Context.forceHead context type_

elaborationFailed :: Context v -> Mode result -> M (result (Syntax.Term v))
elaborationFailed context mode =
  case mode of
    Infer _ -> do
      type_ <- Context.newMetaType context
      type' <- readback context type_
      pure $ Inferred (Syntax.App (Syntax.Global Builtin.fail) Explicit type') type_

    Check type_ -> do
      type' <- readback context type_
      result context mode (Syntax.App (Syntax.Global Builtin.fail) Explicit type') type_

postponeCheck
  :: Context v
  -> Surface.UnspannedTerm
  -> Domain.Type
  -> Meta.Index
  -> M (Checked (Syntax.Term v))
postponeCheck context surfaceTerm expectedType blockingMeta = do
  resultMetaValue <- Context.newMeta context expectedType
  resultMetaTerm <- readback context resultMetaValue
  postponementIndex <- Context.newPostponedCheck context blockingMeta $ \canPostpone -> do
    Checked resultTerm <- elaborateUnspanned context surfaceTerm (Check expectedType) canPostpone
    resultValue <- evaluate context resultTerm
    success <- Context.try_ context $ Unification.unify context Flexibility.Rigid resultValue resultMetaValue
    if success then
      pure resultTerm
    else
      readback context $
        Domain.Neutral (Domain.Global Builtin.fail) $ Domain.Apps $ pure (Explicit, expectedType)
  pure $ Checked $ Syntax.PostponedCheck postponementIndex resultMetaTerm

postponeInference
  :: Context v
  -> Surface.UnspannedTerm
  -> M (Inferred (Syntax.Term v))
postponeInference context surfaceTerm = do
  expectedType <- Context.newMetaType context
  case expectedType of
    Domain.Neutral (Domain.Meta blockingMeta) _ -> do
      Checked term <- postponeCheck context surfaceTerm expectedType blockingMeta
      pure $ Inferred term expectedType

    _ ->
      panic "postponeInfer non-meta"

inferLiteral :: Literal -> Domain.Type
inferLiteral literal =
  case literal of
    Literal.Integer _ ->
      Builtin.Int

inferImplicitApps
  :: Context v
  -> Syntax.Term v
  -> Domain.Value
  -> HashMap Name Surface.Term
  -> Postponement.CanPostpone
  -> M (Syntax.Term v, Domain.Value)
inferImplicitApps context function functionType arguments canPostpone
  | HashMap.null arguments =
    pure (function, functionType)

  | otherwise = do
    (metaArgs, functionType') <-
      insertMetasReturningSyntax context (UntilImplicit (`HashMap.member` arguments)) functionType

    let
      function'' =
        Syntax.apps function metaArgs
    functionType'' <- Context.forceHead context functionType'
    case functionType'' of
      Domain.Pi binding domain Implicit targetClosure
        | let name = Binding.toName binding
        , name `HashMap.member` arguments -> do
          argument' <- check context (arguments HashMap.! name) domain
          argument'' <- evaluate context argument'
          target <- Evaluation.evaluateClosure targetClosure argument''
          inferImplicitApps
            context
            (Syntax.App function'' Implicit argument')
            target
            (HashMap.delete name arguments)
            Postponement.CanPostpone
      _
        | [(name, argument@(Surface.Term argumentSpan _))] <- HashMap.toList arguments -> do
          domain <- Context.newMetaType $ Context.spanned argumentSpan context
          (context', _) <- Context.extend context name domain
          target <- Context.newMetaType context'
          target' <- readback context' target
          let
            targetClosure =
              Domain.Closure (Context.toEnvironment context) target'
            metaFunctionType =
              Domain.Pi (Binding.Unspanned name) domain Implicit targetClosure
          f <- Unification.tryUnify context functionType' metaFunctionType
          argument' <- check context argument domain
          argumentValue <- evaluate context argument'
          target'' <- Evaluation.evaluateClosure targetClosure argumentValue
          pure (Syntax.App (f function'') Implicit argument', target'')

      Domain.Neutral (Domain.Meta blockingMeta) _
        | Postponement.CanPostpone <- canPostpone ->
          postponeImplicitApps context function arguments functionType blockingMeta

      _ -> do
        functionType''' <- readback context functionType'
        pfunction <- Context.toPrettyableTerm context function''
        pfunctionType <- Context.toPrettyableTerm context functionType'''
        Context.report context $
          Error.ImplicitApplicationMismatch
            (HashSet.fromMap $ void arguments)
            pfunction
            pfunctionType
        inferenceFailed context

postponeImplicitApps
  :: Context v
  -> Syntax.Term v
  -> HashMap Name Surface.Term
  -> Domain.Value
  -> Meta.Index
  -> M (Syntax.Term v, Domain.Value)
postponeImplicitApps context function arguments functionType blockingMeta = do
  expectedType <- Context.newMetaType context
  resultMetaValue <- Context.newMeta context expectedType
  resultMetaTerm <- readback context resultMetaValue
  postponementIndex <- Context.newPostponedCheck context blockingMeta $ \canPostpone -> do
    (resultTerm, resultType) <- inferImplicitApps context function functionType arguments canPostpone
    resultValue <- evaluate context resultTerm
    f <- Unification.tryUnify context resultType expectedType
    success <- Context.try_ context $ Unification.unify context Flexibility.Rigid resultMetaValue resultValue
    if success then
      pure $ f resultTerm

    else
      readback context $
        Domain.Neutral (Domain.Global Builtin.fail) $ Domain.Apps $ pure (Explicit, expectedType)
  pure (Syntax.PostponedCheck postponementIndex resultMetaTerm, expectedType)

inferenceFailed :: Context v -> M (Syntax.Term v, Domain.Type)
inferenceFailed context = do
  type_ <- Context.newMetaType context
  type' <- readback context type_
  pure
    ( Syntax.App (Syntax.Global Builtin.fail) Explicit type'
    , type_
    )

checkingFailed :: Context v -> Domain.Type -> M (Syntax.Term v)
checkingFailed context type_ = do
  type' <- readback context type_
  pure $ Syntax.App (Syntax.Global Builtin.fail) Explicit type'

-------------------------------------------------------------------------------
-- Constructor name resolution

data ResolvedConstructor
  = Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | ResolvedConstructor !Name.QualifiedConstructor
  | ResolvedData !Name.Qualified
  deriving Show

resolveConstructor
  :: HashSet Name.QualifiedConstructor
  -> HashSet Name.Qualified
  -> M (Maybe (Either Meta.Index Name.Qualified))
  -> M (Either Meta.Index ResolvedConstructor)
resolveConstructor constructorCandidates dataCandidates getExpectedTypeName_ =
  case (toList constructorCandidates, toList dataCandidates) of
    ([constr], []) ->
      pure $ Right $ ResolvedConstructor constr

    ([], [data_]) ->
      pure $ Right $ ResolvedData data_

    _ -> do
      maybeExpectedTypeName <- getExpectedTypeName_
      pure $ case maybeExpectedTypeName of
        Nothing ->
          Right $ Ambiguous constructorCandidates dataCandidates

        Just (Left blockingMeta) ->
          Left blockingMeta

        Just (Right Builtin.TypeName) ->
          case toList dataCandidates of
            [data_] ->
              Right $ ResolvedData data_

            _ ->
              Right $ Ambiguous mempty dataCandidates

        Just (Right expectedTypeName) -> do
          let
            constrs' =
              HashSet.filter
                (\(Name.QualifiedConstructor constrTypeName _) -> constrTypeName == expectedTypeName)
                constructorCandidates
          case toList constrs' of
            [constr] ->
              Right $ ResolvedConstructor constr

            _ ->
              Right $ Ambiguous constrs' mempty

getModeExpectedTypeName
  :: Context v
  -> Mode x
  -> M (Maybe (Either Meta.Index Name.Qualified))
getModeExpectedTypeName context mode =
  case mode of
    Infer m ->
      m

    Check expectedType ->
      getExpectedTypeName context expectedType

getExpectedTypeName
  :: Context v
  -> Domain.Type
  -> M (Maybe (Either Meta.Index Name.Qualified))
getExpectedTypeName context type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Domain.Neutral (Domain.Meta blockingMeta) _ ->
      pure $ Just $ Left blockingMeta

    Domain.Neutral (Domain.Global name) _ ->
      pure $ Just $ Right name

    Domain.Neutral (Domain.Var _) _ ->
      pure Nothing

    Domain.Con {} ->
      pure Nothing

    Domain.Lit {} ->
      pure Nothing

    Domain.Glued _ _ value -> do
      value' <- force value
      getExpectedTypeName context value'

    Domain.Pi binding domain _ targetClosure -> do
      (context', var) <- Context.extend context (Binding.toName binding) domain
      target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
      getExpectedTypeName context' target

    Domain.Fun _ _ target ->
      getExpectedTypeName context target

    Domain.Lam {} ->
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
  -> Surface.Term
  -> M (Maybe (Either Meta.Index Name.Qualified))
  -> M (Syntax.Term v, Domain.Type)
inferAndInsertMetas context until term@(Surface.Term span _) expectedTypeName = do
  Inferred term' type_ <- infer context term expectedTypeName
  (args, type') <- insertMetasReturningSyntax context until type_
  pure (Syntax.Spanned span $ Syntax.apps term' args, type')

insertMetasReturningSyntax
  :: Context v
  -> InsertUntil
  -> Domain.Type
  -> M ([(Plicity, Syntax.Term v)], Domain.Type)
insertMetasReturningSyntax context until type_ = do
  (args, res) <- insertMetas context until type_
  args' <- mapM (mapM $ readback context) args
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
      meta <- Context.newMeta context domain
      (args, res) <- insertMetas context until target
      pure ((plicity, meta) : args, res)

    (UntilExplicit, Domain.Pi _ domain Implicit targetClosure) ->
      instantiate domain Implicit targetClosure

    (UntilImplicit stopAt, Domain.Pi binding domain Implicit targetClosure)
      | not $ stopAt $ Binding.toName binding ->
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
      meta <- Context.newMeta context domain
      target <- Evaluation.evaluateClosure targetClosure meta
      (args, res) <- insertMetas context until target
      pure ((plicity, meta) : args, res)

isSubtype
  :: Context v
  -> Domain.Type
  -> Domain.Type
  -> M Bool
isSubtype context type1 type2 = do
  type2' <- Context.forceHead context type2
  case type2' of
    Domain.Pi binding domain plicity targetClosure
      | case plicity of
          Explicit -> False
          Implicit -> True
          Constraint -> True
      -> do
        let
          name =
            Binding.toName binding
        (context', var) <- Context.extend context name domain
        target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
        isSubtype context' type1 target

    _ -> do
      (_, type1') <- insertMetasReturningSyntax context UntilExplicit type1
      Context.try_ context $ Unification.unify context Flexibility.Rigid type1' type2

-------------------------------------------------------------------------------
-- Meta solutions

checkMetaSolutions
  :: Context Void
  -> Meta.Vars
  -> M Syntax.MetaSolutions
checkMetaSolutions context metaVars =
  flip IntMap.traverseWithKey (Meta.vars metaVars) $ \index var ->
    case var of
      Meta.Unsolved type_ _ _ span -> do
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
          (context'', _) <- Context.extend context' "x" domain
          body <- addLambdas context'' target
          pure $ Syntax.Lam "x" domain' Explicit body

        Domain.Pi binding domain Explicit targetClosure -> do
          let
            name =
              Binding.toName binding
          domain' <- readback context' domain
          (context'', var) <- Context.extend context' name domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          body <- addLambdas context'' target
          pure $ Syntax.Lam (Bindings.Unspanned name) domain' Explicit body

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
