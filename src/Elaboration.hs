{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Elaboration where

import Boxity
import qualified Builtin
import Control.Exception.Lifted (try)
import Core.Binding (Binding)
import qualified Core.Binding as Binding
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import Data.Coerce
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef.Lifted
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Some (Some)
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
import Prettyprinter (Doc)
import Protolude hiding (IntMap, IntSet, Seq, check, evaluate, force, try, until)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import Telescope (Telescope)
import qualified Telescope
import Var (Var)
import qualified Var

inferTopLevelDefinition ::
  Scope.DefinitionKind ->
  Name.Qualified ->
  Surface.Definition ->
  M ((Syntax.Definition, Syntax.Type Void, Meta.EagerState), [Error])
inferTopLevelDefinition definitionKind defName def = do
  context <- Context.empty definitionKind defName
  (def', type_) <- inferDefinition context def
  postponed <- readIORef $ Context.postponed context
  metaVars <- readIORef $ Context.metas context
  errors <- readIORef $ Context.errors context
  let zonkedDef = ZonkPostponedChecks.zonkDefinition postponed def'
  eagerMetaVars <- Meta.toEagerState metaVars zonkedDef $ Just type_
  pure ((zonkedDef, type_, eagerMetaVars), toList errors)

checkTopLevelDefinition ::
  Scope.DefinitionKind ->
  Name.Qualified ->
  Surface.Definition ->
  Domain.Type ->
  M ((Syntax.Definition, Meta.EagerState), [Error])
checkTopLevelDefinition definitionKind defName def type_ = do
  context <- Context.empty definitionKind defName
  def' <- checkDefinition context def type_
  postponed <- readIORef $ Context.postponed context
  metaVars <- readIORef $ Context.metas context
  errors <- readIORef $ Context.errors context
  let zonkedDef = ZonkPostponedChecks.zonkDefinition postponed def'
  eagerMetaVars <- Meta.toEagerState metaVars zonkedDef Nothing
  pure ((zonkedDef, eagerMetaVars), toList errors)

checkDefinitionMetaSolutions ::
  Scope.DefinitionKind ->
  Name.Qualified ->
  Syntax.Definition ->
  Syntax.Type Void ->
  Meta.EagerState ->
  M ((Syntax.Definition, Syntax.Type Void), [Error])
checkDefinitionMetaSolutions definitionKind defName def type_ metas = do
  context <- Context.empty definitionKind defName
  metasVar <- newIORef $ Meta.fromEagerState metas
  let context' = context {Context.metas = metasVar}
  metas' <- checkMetaSolutions context' metas
  (def', type') <- MetaInlining.inlineSolutions metas' def type_
  def'' <- Inlining.inlineDefinition def'
  type'' <- Inlining.inlineTerm Environment.empty type'
  errors <- readIORef $ Context.errors context'
  pure ((def'', type''), toList errors)

checkDefinition ::
  Context Void ->
  Surface.Definition ->
  Domain.Type ->
  M Syntax.Definition
checkDefinition context def expectedType =
  case def of
    Surface.TypeDeclaration _ type_ -> do
      type' <- check context type_ expectedType
      postProcessDefinition context $ Syntax.TypeDeclaration type'
    Surface.ConstantDefinition clauses -> do
      let clauses' =
            [Clauses.Clause clause mempty | (_, clause) <- clauses]
      term' <- Clauses.check context clauses' expectedType
      postProcessDefinition context $ Syntax.ConstantDefinition term'
    Surface.DataDefinition _span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs mempty
      type' <- evaluate context type_
      success <- Context.try_ context $ Unification.unify context Flexibility.Rigid type' expectedType
      if success
        then postProcessDataDefinition context boxity tele
        else do
          expectedType' <- readback context expectedType
          postProcessDefinition context $
            Syntax.ConstantDefinition $
              Builtin.unknown expectedType'

inferDefinition ::
  Context Void ->
  Surface.Definition ->
  M (Syntax.Definition, Syntax.Type Void)
inferDefinition context def =
  case def of
    Surface.TypeDeclaration _ type_ -> do
      type' <- check context type_ Builtin.Type
      def' <- postProcessDefinition context $ Syntax.TypeDeclaration type'
      pure (def', Builtin.type_)
    Surface.ConstantDefinition clauses -> do
      let clauses' =
            [Clauses.Clause clause mempty | (_, clause) <- clauses]
      (term', type_) <- Clauses.infer context clauses'
      type' <- readback context type_
      def' <- postProcessDefinition context $ Syntax.ConstantDefinition term'
      pure (def', type')
    Surface.DataDefinition _span boxity params constrs -> do
      (tele, type_) <- inferDataDefinition context params constrs mempty
      def' <- postProcessDataDefinition context boxity tele
      pure (def', type_)

postProcessDefinition :: Context v -> Syntax.Definition -> M Syntax.Definition
postProcessDefinition context def = do
  Context.inferAllPostponedChecks context
  postponed <- readIORef $ Context.postponed context
  pure $ ZonkPostponedChecks.zonkDefinition postponed def

-------------------------------------------------------------------------------

inferDataDefinition ::
  Context v ->
  [(Surface.SpannedName, Surface.Type, Plicity)] ->
  [Surface.ConstructorDefinition] ->
  Tsil (Plicity, Var) ->
  M (Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v, Syntax.Type v)
inferDataDefinition context surfaceParams constrs paramVars =
  case surfaceParams of
    [] -> do
      thisType <-
        Syntax.fromVoid
          <$> Context.varPis
            context
            Environment.empty
            (toList paramVars)
            Builtin.Type

      thisType' <- evaluate context thisType
      let context' = context {Context.definitionType = Just thisType'}
      constrs' <- forM constrs $ \case
        Surface.GADTConstructors cs type_ -> do
          type' <- check context' type_ Builtin.Type
          pure [(constr, type') | (_, constr) <- cs]
        Surface.ADTConstructor _ constr types -> do
          types' <- forM types $ \type_ ->
            check context' type_ Builtin.Type

          returnType <-
            readback context' $
              Domain.Neutral (Domain.Global $ Context.definitionName context') $
                Domain.Apps $ second Domain.var <$> paramVars
          let type_ =
                Syntax.funs types' Explicit returnType
          pure [(constr, type_)]
      pure
        ( Telescope.Empty $ Syntax.ConstructorDefinitions $ OrderedHashMap.fromList $ concat constrs'
        , Syntax.Global Builtin.TypeName
        )
    (spannedName@(Surface.SpannedName _ name), type_, plicity) : surfaceParams' -> do
      type' <- check context type_ Builtin.Type
      type'' <- lazyEvaluate context type'
      (context', paramVar) <- Context.extendSurface context name type''
      let paramVars' =
            paramVars Tsil.:> (plicity, paramVar)

          binding =
            Binding.fromSurface spannedName
      (tele, dataType) <- inferDataDefinition context' surfaceParams' constrs paramVars'
      pure
        ( Telescope.Extend binding type' plicity tele
        , Syntax.Pi binding type' plicity dataType
        )

postProcessDataDefinition ::
  Context Void ->
  Boxity.Boxity ->
  Telescope Binding Syntax.Type Syntax.ConstructorDefinitions Void ->
  M Syntax.Definition
postProcessDataDefinition outerContext boxity outerTele = do
  Context.inferAllPostponedChecks outerContext
  postponed <- readIORef $ Context.postponed outerContext
  Syntax.DataDefinition boxity <$> go outerContext postponed outerTele mempty
  where
    go ::
      Context v ->
      Postponed.Checks ->
      Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v ->
      Tsil (Plicity, Var) ->
      M (Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v)
    go context postponed tele paramVars =
      case tele of
        Telescope.Empty (Syntax.ConstructorDefinitions constructorDefinitions) -> do
          map (Telescope.Empty . Syntax.ConstructorDefinitions) $
            OrderedHashMap.forMUnordered constructorDefinitions $ \constructorType -> do
              let zonkedConstructorType =
                    ZonkPostponedChecks.zonkTerm postponed constructorType
              maybeConstructorType <- Context.try context $ addConstructorIndexEqualities context paramVars zonkedConstructorType
              pure $ fromMaybe (Builtin.unknown Builtin.type_) maybeConstructorType
        Telescope.Extend name type_ plicity tele' -> do
          typeValue <- lazyEvaluate context type_
          (context', paramVar) <- Context.extend context (Binding.toName name) typeValue
          let zonkedType =
                ZonkPostponedChecks.zonkTerm postponed type_
          Telescope.Extend name zonkedType plicity <$> go context' postponed tele' (paramVars Tsil.:> (plicity, paramVar))

addConstructorIndexEqualities :: Context v -> Tsil (Plicity, Var) -> Syntax.Term v -> M (Syntax.Term v)
addConstructorIndexEqualities context paramVars constrType =
  case constrType of
    Syntax.Spanned span' constrType' -> do
      constrType'' <- addConstructorIndexEqualities (Context.spanned span' context) paramVars constrType'
      pure $ Syntax.Spanned span' constrType''
    Syntax.Pi binding domain plicity target -> do
      domain' <- lazyEvaluate context domain
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
    dataName = Context.definitionName context

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
          f <-
            Unification.tryUnify
              context'
              constrTypeValue
              ( Domain.Neutral
                  (Domain.Global dataName)
                  (Domain.Apps $ second Domain.var <$> paramVars)
              )
          f <$> readback context' constrTypeValue

    termIndexEqualities ::
      Context v ->
      [(Plicity, Syntax.Term v)] ->
      [(Plicity, Var)] ->
      Syntax.Term v ->
      Tsil (Plicity, Syntax.Term v) ->
      M (Syntax.Term v)
    termIndexEqualities context' indices paramVars' hd params =
      case (indices, paramVars') of
        ((plicity1, index) : indices', (plicity2, paramVar) : paramVars'')
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
                let domain =
                      Builtin.equals paramType index param

                target <- termIndexEqualities context' indices' paramVars'' hd (params Tsil.:> (plicity1, param))
                pure $ Syntax.Fun domain Constraint target
          | otherwise ->
            panic "indexEqualities plicity mismatch"
        ([], []) ->
          pure $ Syntax.apps hd params
        _ ->
          panic "indexEqualities length mismatch"

    valueIndexEqualities ::
      Context v ->
      [(Plicity, Domain.Value)] ->
      [(Plicity, Var)] ->
      M (Syntax.Term v)
    valueIndexEqualities context' indices paramVars' =
      case (indices, paramVars') of
        ((plicity1, index) : indices', (plicity2, paramVar) : paramVars'')
          | plicity1 == plicity2 -> do
            index' <- Context.forceHead context' index
            case index' of
              Domain.Neutral (Domain.Var indexVar) Domain.Empty
                | indexVar == paramVar ->
                  valueIndexEqualities context' indices' paramVars''
              _ -> do
                let domain =
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

check ::
  Context v ->
  Surface.Term ->
  Domain.Type ->
  M (Syntax.Term v)
check context term type_ =
  coerce $ elaborate context term $ Check type_

infer ::
  Context v ->
  Surface.Term ->
  M (Maybe (Either Meta.Index Name.Qualified)) ->
  M (Inferred (Syntax.Term v))
infer context term expectedTypeName =
  elaborate context term $ Infer expectedTypeName

data Inferred t = Inferred t Domain.Type
  deriving (Functor)

newtype Checked t = Checked t
  deriving (Functor)

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
elaborate context term@(Surface.Term span _) mode =
  elaborateWith (Context.spanned span context) term mode Postponement.CanPostpone

elaborateWith ::
  Functor result =>
  Context v ->
  Surface.Term ->
  Mode result ->
  Postponement.CanPostpone ->
  M (result (Syntax.Term v))
elaborateWith context spannedTerm@(Surface.Term span term) mode canPostpone = do
  mode' <- forceExpectedTypeHead context mode
  case (term, mode') of
    (Surface.Lam (Surface.ExplicitPattern pat) body, Check (Domain.Pi piBinding domain Explicit targetClosure)) -> do
      let name =
            Binding.toName piBinding
      (context', var) <- Context.extend context name domain
      domain' <- readback context domain
      target <- Evaluation.evaluateClosure targetClosure (Domain.var var)
      body' <- Matching.checkSingle context' var Explicit pat body target
      binding <- SuggestedName.patternBinding context pat name
      pure $ Checked $ Syntax.Spanned span $ Syntax.Lam binding domain' Explicit body'
    (Surface.Lam (Surface.ExplicitPattern pat) body, Check (Domain.Fun domain Explicit target)) -> do
      domain' <- readback context domain
      binding <- SuggestedName.patternBinding context pat "x"
      (context', var) <- Context.extend context (Bindings.toName binding) domain
      body' <- Matching.checkSingle context' var Explicit pat body target
      pure $ Checked $ Syntax.Spanned span $ Syntax.Lam binding domain' Explicit body'
    (Surface.Lam (Surface.ImplicitPattern _ namedPats) body, _)
      | HashMap.null namedPats ->
        elaborate context body mode
    (Surface.Lam (Surface.ImplicitPattern patsSpan namedPats) body, Check (Domain.Pi piBinding domain Implicit targetClosure))
      | let name = Binding.toName piBinding
        , Just patBinding <- HashMap.lookup name namedPats -> do
        let body' =
              Surface.Term span $
                Surface.Lam (Surface.ImplicitPattern patsSpan (HashMap.delete name namedPats)) body

        (context', var) <- Context.extend context name domain
        domain' <- readback context domain
        target <- Evaluation.evaluateClosure targetClosure (Domain.var var)
        body'' <- Matching.checkSingle context' var Implicit (Surface.pattern_ patBinding) body' target
        binding <- SuggestedName.patternBinding context (Surface.pattern_ patBinding) name
        let lamSpan
              | Surface.isTextuallyFirst patBinding = span
              | otherwise = Span.add (Surface.spanIncludingName patBinding) span
        pure $ Checked $ Syntax.Spanned lamSpan $ Syntax.Lam binding domain' Implicit body''
    (_, Check expectedType@(Domain.Pi binding domain plicity targetClosure))
      | isImplicitish plicity ->
        do
          let checkUnderBinder = do
                let name =
                      Binding.toName binding
                (context', var) <- Context.extend context name domain
                target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
                domain' <- readback context domain
                Checked term' <- elaborate context' spannedTerm $ Check target
                pure $ Checked $ Syntax.Lam (Bindings.Unspanned name) domain' plicity $ Syntax.Spanned span term'

          case term of
            Surface.Var varName
              | Just (value, type_) <- Context.lookupSurfaceName varName context -> do
                type' <- Context.forceHead context type_
                case type' of
                  -- Approximate polymorphic variable inference
                  Domain.Neutral (Domain.Meta _) _ -> do
                    success <- Context.try_ context $ Unification.unify context Flexibility.Rigid type' expectedType
                    term' <- readback context $ if success then value else Builtin.Unknown expectedType
                    pure $ Checked $ Syntax.Spanned span term'
                  _ ->
                    checkUnderBinder
            _ ->
              checkUnderBinder
    (_, Check expectedType@(Domain.Neutral (Domain.Meta blockingMeta) _))
      | Postponement.CanPostpone <- canPostpone ->
        postponeCheck context spannedTerm expectedType blockingMeta
    (Surface.Lam plicitPattern body@(Surface.Term bodySpan _), _) -> do
      let patternSpan =
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
              (Syntax.Spanned span $ Syntax.Lam binding domain' plicity body')
              ( Domain.Pi (Binding.Unspanned name) domain plicity $
                  Domain.Closure (Context.toEnvironment context) target'
              )

      case (canPostpone, plicitPattern, mode') of
        (Postponement.CanPostpone, _, Infer _) -> do
          postponeInference context spannedTerm
        (_, Surface.ExplicitPattern pat, _) ->
          elaborateLambda Explicit "x" pat result
        (_, Surface.ImplicitPattern _ (HashMap.toList -> [(name, patBinding)]), _) -> do
          elaborateLambda Implicit name (Surface.pattern_ patBinding) implicitLambdaResult
        (_, Surface.ImplicitPattern _ _, _) -> do
          Context.report (Context.spanned patternSpan context) Error.UnableToInferImplicitLambda
          elaborationFailed context mode
    (Surface.Var name, _) ->
      case Context.lookupSurfaceName name context of
        Just (value, type_) -> do
          term' <- readback context value
          result context mode (Syntax.Spanned span term') type_
        Nothing -> do
          maybeScopeEntry <- fetch $ Query.ResolvedName (Context.moduleName context) name

          case maybeScopeEntry of
            Nothing -> do
              Context.report context $ Error.NotInScope name
              elaborationFailed context mode
            Just (Scope.Name qualifiedName)
              | qualifiedName == Context.definitionName context
                , Just type_ <- Context.definitionType context ->
                result context mode (Syntax.Spanned span $ Syntax.Global qualifiedName) type_
              | otherwise -> do
                typeResult <- try $ fetch $ Query.ElaboratedType qualifiedName
                case typeResult of
                  Left (Cyclic (_ :: Some Query)) -> do
                    Context.report context $ Error.NotInScope name
                    elaborationFailed context mode
                  Right type_ -> do
                    type' <- evaluate context $ Syntax.fromVoid type_
                    result context mode (Syntax.Spanned span $ Syntax.Global qualifiedName) type'
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
                      postponeInference context spannedTerm
                    (Postponement.CanPostpone, Check expectedType) ->
                      postponeCheck context spannedTerm expectedType blockingMeta
                    (Postponement.Can'tPostpone, _) -> do
                      Context.report context $ Error.Ambiguous name constructorCandidates dataCandidates
                      elaborationFailed context mode
                Right (Ambiguous constrCandidates' dataCandidates') -> do
                  Context.report context $ Error.Ambiguous name constrCandidates' dataCandidates'
                  elaborationFailed context mode
                Right (ResolvedConstructor constr) -> do
                  type_ <- fetch $ Query.ConstructorType constr
                  type' <- evaluate context $ Syntax.fromVoid $ Telescope.fold Syntax.implicitPi type_
                  result context mode (Syntax.Spanned span $ Syntax.Con constr) type'
                Right (ResolvedData data_)
                  | data_ == Context.definitionName context
                    , Just type_ <- Context.definitionType context ->
                    result context mode (Syntax.Spanned span $ Syntax.Global data_) type_
                  | otherwise -> do
                    typeResult <- try $ fetch $ Query.ElaboratedType data_
                    case typeResult of
                      Left (Cyclic (_ :: Some Query)) -> do
                        Context.report context $ Error.NotInScope name
                        elaborationFailed context mode
                      Right type_ -> do
                        type' <- evaluate context $ Syntax.fromVoid type_
                        result context mode (Syntax.Spanned span $ Syntax.Global data_) type'
            Just (Scope.Ambiguous constrCandidates dataCandidates) -> do
              Context.report context $ Error.Ambiguous name constrCandidates dataCandidates
              elaborationFailed context mode
    (Surface.Lit lit, _) ->
      result context mode (Syntax.Spanned span $ Syntax.Lit lit) (inferLiteral lit)
    (Surface.Lets lets body, _) ->
      map Syntax.Lets <$> elaborateLets context mempty mempty mempty lets body mode
    (Surface.Pi spannedName@(Surface.SpannedName _ name) plicity domain target, _) -> do
      domain' <- check context domain Builtin.Type
      domain'' <- lazyEvaluate context domain'

      (context', _) <- Context.extendSurface context name domain''

      target' <- check context' target Builtin.Type
      result
        context
        mode
        (Syntax.Spanned span $ Syntax.Pi (Binding.fromSurface spannedName) domain' plicity target')
        Builtin.Type
    (Surface.Fun domain target, _) -> do
      domain' <- check context domain Builtin.Type
      target' <- check context target Builtin.Type
      result context mode (Syntax.Spanned span $ Syntax.Fun domain' Explicit target') Builtin.Type
    (Surface.Case scrutinee branches, _) -> do
      skipContext <- Context.skip context
      (scrutinee', scrutineeType) <- inferAndInsertMetas skipContext UntilExplicit scrutinee $ pure Nothing
      case mode of
        Infer _ -> do
          expectedType <- Context.newMetaType context
          term' <- Matching.checkCase context scrutinee' scrutineeType branches expectedType Postponement.CanPostpone
          pure $ Inferred (Syntax.Spanned span term') expectedType
        Check expectedType -> do
          term' <- Matching.checkCase context scrutinee' scrutineeType branches expectedType Postponement.CanPostpone
          pure $ Checked $ Syntax.Spanned span term'
    (Surface.App function@(Surface.Term functionSpan _) argument@(Surface.Term argumentSpan _), _) -> do
      (function', functionType) <- inferAndInsertMetas context UntilExplicit function $ getModeExpectedTypeName context mode
      functionType' <- Context.forceHead context functionType

      case functionType' of
        Domain.Pi _ domain Explicit targetClosure -> do
          argument' <- check context argument domain
          argument'' <- lazyEvaluate context argument'
          target <- Evaluation.evaluateClosure targetClosure argument''
          result context mode (Syntax.Spanned span $ Syntax.App function' Explicit argument') target
        Domain.Fun domain Explicit target -> do
          argument' <- check context argument domain
          result context mode (Syntax.Spanned span $ Syntax.App function' Explicit argument') target
        _ -> do
          domain <- Context.newMetaType $ Context.spanned argumentSpan context
          (context', _) <- Context.extend context "x" domain
          target <- Context.newMetaType context'
          target' <- readback context' target
          let targetClosure =
                Domain.Closure (Context.toEnvironment context) target'
              metaFunctionType =
                Domain.Pi (Binding.Unspanned "x") domain Explicit targetClosure
          f <- Unification.tryUnify (Context.spanned functionSpan context) functionType metaFunctionType
          argument' <- check context argument domain
          argumentValue <- lazyEvaluate context argument'
          target'' <- Evaluation.evaluateClosure targetClosure argumentValue
          result context mode (Syntax.Spanned span $ Syntax.App (f function') Explicit argument') target''
    (Surface.ImplicitApps function arguments, _) -> do
      Inferred function' functionType <- infer context function $ getModeExpectedTypeName context mode
      (result_, resultType) <- inferImplicitApps context function' functionType arguments Postponement.CanPostpone
      result context mode (Syntax.Spanned span result_) resultType
    (Surface.Wildcard, Check expectedType) -> do
      term' <- Context.newMeta context expectedType
      Checked . Syntax.Spanned span <$> readback context term'
    (Surface.Wildcard, Infer _) -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta context type_
      term'' <- readback context term'
      pure $ Inferred (Syntax.Spanned span term'') type_
    (Surface.ParseError err, _) -> do
      Context.reportParseError context err
      elaborateWith context (Surface.Term span Surface.Wildcard) mode Postponement.CanPostpone

data LetBoundTerm where
  LetBoundTerm :: Context v -> Syntax.Term v -> LetBoundTerm

elaborateLets ::
  Functor result =>
  Context v ->
  HashMap Name.Surface (Span.Relative, Var) ->
  IntMap Var (Span.Relative, Name.Surface) ->
  Tsil (Var, LetBoundTerm) ->
  [Surface.Let] ->
  Surface.Term ->
  Mode result ->
  M (result (Syntax.Lets v))
elaborateLets context declaredNames undefinedVars definedVars lets body mode = do
  case lets of
    [] -> do
      body' <- elaborate context body mode
      foldlM reportUndefinedName (Syntax.In <$> body') (IntMap.toList undefinedVars)
      where
        reportUndefinedName lets' (var, (span, surfaceName@(Name.Surface nameText))) = do
          Context.report (Context.spanned span context) $ Error.UndefinedLetName surfaceName
          let index =
                fromMaybe (panic "elaborateLets: indexless var") $ Context.lookupVarIndex var context

              type_ = Context.lookupVarType var context
          term <- readback context $ Builtin.Unknown type_
          pure $ Syntax.Let (Bindings.Unspanned $ Name.Name nameText) index term <$> lets'

    -- Optimisation: No need to consider the rest of the bindings to be mutuals if they're all defined
    _
      | IntMap.null undefinedVars
        , not (Tsil.null definedVars) -> do
        lets' <- elaborateLets context mempty mempty mempty lets body mode
        pure $ Syntax.In . Syntax.Lets <$> lets'
    Surface.LetType spannedName@(Surface.SpannedName span surfaceName) type_ : lets' ->
      case HashMap.lookup surfaceName declaredNames of
        Just (previousSpan, _) -> do
          Context.report (Context.spanned span context) $ Error.DuplicateLetName surfaceName previousSpan
          elaborateLets context declaredNames undefinedVars definedVars lets' body mode
        Nothing -> do
          typeTerm <- check context type_ Builtin.Type
          typeValue <- lazyEvaluate context typeTerm
          (context', var) <- Context.extendSurface context surfaceName typeValue
          let declaredNames' =
                HashMap.insert surfaceName (span, var) declaredNames

              undefinedVars' =
                IntMap.insert var (span, surfaceName) undefinedVars
          lets'' <- elaborateLets context' declaredNames' undefinedVars' definedVars lets' body mode
          pure $ Syntax.LetType (Binding.fromSurface spannedName) typeTerm <$> lets''
    Surface.Let surfaceName@(Name.Surface nameText) clauses : lets' -> do
      let clauses' =
            [Clauses.Clause clause mempty | (_, clause) <- clauses]

          name =
            Name.Name nameText

          bindings =
            Bindings.fromName (map fst clauses) name

          span =
            case clauses of
              (span_, _) : _ ->
                span_
              _ ->
                panic "elaborateLets: Clauseless Surface.Let"

      case HashMap.lookup surfaceName declaredNames of
        Nothing -> do
          skipContext <- Context.skip context
          (boundTerm, typeValue) <- Clauses.infer skipContext clauses'
          typeTerm <- readback context typeValue
          boundValue <- lazyEvaluate skipContext boundTerm
          (context', var) <- Context.extendSurfaceDef context surfaceName boundValue typeValue
          let declaredNames' =
                HashMap.insert surfaceName (span, var) declaredNames

              definedVars' =
                definedVars Tsil.:> (var, LetBoundTerm skipContext boundTerm)
          lets'' <- elaborateLets context' declaredNames' undefinedVars definedVars' lets' body mode
          pure $
            Syntax.LetType (Binding.Unspanned name) typeTerm
              . Syntax.Let bindings Index.Zero boundTerm
              <$> lets''
        Just (previousSpan, var) -> do
          case Context.lookupVarValue var context of
            Just _ -> do
              Context.report (Context.spanned span context) $ Error.DuplicateLetName surfaceName previousSpan
              elaborateLets context declaredNames undefinedVars definedVars lets' body mode
            Nothing -> do
              let type_ =
                    Context.lookupVarType var context
              boundTerm <- Clauses.check context clauses' type_
              let index =
                    fromMaybe (panic "elaborateLets: indexless var") $ Context.lookupVarIndex var context

                  undefinedVars' =
                    IntMap.delete var undefinedVars

                  definedVars' =
                    definedVars Tsil.:> (var, LetBoundTerm context boundTerm)
              redefinedContext <- mdo
                values <- forM definedVars' $ \(var', LetBoundTerm context' boundTerm') ->
                  (var',) <$> lazyEvaluate (defines context' values) boundTerm'
                pure $ defines context values
              lets'' <- elaborateLets redefinedContext declaredNames undefinedVars' definedVars' lets' body mode
              pure $ Syntax.Let bindings index boundTerm <$> lets''
  where
    defines :: Context v -> Tsil (Var, Domain.Value) -> Context v
    defines =
      foldr' $ \(var, value) context' ->
        if isJust $ Context.lookupVarIndex var context'
          then Context.defineWellOrdered context' var value
          else context'

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
      pure $ Inferred (Builtin.unknown type') type_
    Check type_ -> do
      type' <- readback context type_
      result context mode (Builtin.unknown type') type_

postponeCheck ::
  Context v ->
  Surface.Term ->
  Domain.Type ->
  Meta.Index ->
  M (Checked (Syntax.Term v))
postponeCheck context surfaceTerm expectedType blockingMeta =
  fmap Checked $
    postpone context expectedType blockingMeta $ \canPostpone -> do
      Checked resultTerm <- elaborateWith context surfaceTerm (Check expectedType) canPostpone
      pure resultTerm

postponeInference ::
  Context v ->
  Surface.Term ->
  M (Inferred (Syntax.Term v))
postponeInference context surfaceTerm = do
  (blockingMeta, _, expectedType) <- Context.newMetaReturningIndex context Builtin.Type
  Checked term <- postponeCheck context surfaceTerm expectedType blockingMeta
  pure $ Inferred term expectedType

inferLiteral :: Literal -> Domain.Type
inferLiteral literal =
  case literal of
    Literal.Integer _ ->
      Builtin.Int

inferImplicitApps ::
  Context v ->
  Syntax.Term v ->
  Domain.Value ->
  HashMap Name Surface.Term ->
  Postponement.CanPostpone ->
  M (Syntax.Term v, Domain.Value)
inferImplicitApps context function functionType arguments canPostpone
  | HashMap.null arguments =
    pure (function, functionType)
  | otherwise = do
    (metaArgs, functionType') <-
      insertMetasReturningSyntax context (UntilImplicit (`HashMap.member` arguments)) functionType

    let function'' =
          Syntax.apps function metaArgs
    functionType'' <- Context.forceHead context functionType'
    case functionType'' of
      Domain.Pi binding domain Implicit targetClosure
        | let name = Binding.toName binding
          , name `HashMap.member` arguments -> do
          argument' <- check context (arguments HashMap.! name) domain
          argument'' <- lazyEvaluate context argument'
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
          let targetClosure =
                Domain.Closure (Context.toEnvironment context) target'
              metaFunctionType =
                Domain.Pi (Binding.Unspanned name) domain Implicit targetClosure
          f <- Unification.tryUnify context functionType' metaFunctionType
          argument' <- check context argument domain
          argumentValue <- lazyEvaluate context argument'
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

postponeImplicitApps ::
  Context v ->
  Syntax.Term v ->
  HashMap Name Surface.Term ->
  Domain.Value ->
  Meta.Index ->
  M (Syntax.Term v, Domain.Value)
postponeImplicitApps context function arguments functionType blockingMeta = do
  expectedType <- Context.newMetaType context
  postponedTerm <- postpone context expectedType blockingMeta $ \canPostpone -> do
    (resultTerm, resultType) <- inferImplicitApps context function functionType arguments canPostpone
    f <- Unification.tryUnify context resultType expectedType
    pure $ f resultTerm
  pure (postponedTerm, expectedType)

inferenceFailed :: Context v -> M (Syntax.Term v, Domain.Type)
inferenceFailed context = do
  type_ <- Context.newMetaType context
  type' <- readback context type_
  pure
    ( Builtin.unknown type'
    , type_
    )

checkingFailed :: Context v -> Domain.Type -> M (Syntax.Term v)
checkingFailed context type_ =
  readback context $ Builtin.Unknown type_

-------------------------------------------------------------------------------
-- Postponement

postpone ::
  Context v ->
  Domain.Type ->
  Meta.Index ->
  (Postponement.CanPostpone -> M (Syntax.Term v)) ->
  M (Syntax.Term v)
postpone context expectedType blockingMeta check_ = do
  (resultMeta, resultMetaArgs, resultMetaValue) <- Context.newMetaReturningIndex context expectedType
  resultMetaTerm <- readback context resultMetaValue
  postponementIndex <- Context.newPostponedCheck context blockingMeta $ \canPostpone -> do
    resultTerm <- check_ canPostpone
    metaValue <- Context.lookupEagerMeta context resultMeta
    let metaSolution = do
          resultValue <- evaluate context resultTerm
          Unification.checkSolution context resultMeta resultMetaArgs resultValue

    success <- case metaValue of
      Meta.EagerSolved {} -> do
        resultValue <- evaluate context resultTerm
        Context.try_ context $ Unification.unify context Flexibility.Rigid resultValue resultMetaValue
      Meta.EagerUnsolved _ _ postponements _
        | IntSet.null postponements -> do
          lazySolution <- lazy metaSolution
          Context.lazilySolveMeta context resultMeta lazySolution
          pure True
        | otherwise -> do
          solution <- metaSolution
          Context.solveMeta context resultMeta solution
          pure True

    if success
      then pure resultTerm
      else readback context $ Builtin.Unknown expectedType
  pure $ Syntax.PostponedCheck postponementIndex resultMetaTerm

-------------------------------------------------------------------------------
-- Constructor name resolution

data ResolvedConstructor
  = Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | ResolvedConstructor !Name.QualifiedConstructor
  | ResolvedData !Name.Qualified
  deriving (Show)

resolveConstructor ::
  HashSet Name.QualifiedConstructor ->
  HashSet Name.Qualified ->
  M (Maybe (Either Meta.Index Name.Qualified)) ->
  M (Either Meta.Index ResolvedConstructor)
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
          let constrs' =
                HashSet.filter
                  (\(Name.QualifiedConstructor constrTypeName _) -> constrTypeName == expectedTypeName)
                  constructorCandidates
          case toList constrs' of
            [constr] ->
              Right $ ResolvedConstructor constr
            _ ->
              Right $ Ambiguous constrs' mempty

getModeExpectedTypeName ::
  Context v ->
  Mode x ->
  M (Maybe (Either Meta.Index Name.Qualified))
getModeExpectedTypeName context mode =
  case mode of
    Infer m ->
      m
    Check expectedType ->
      getExpectedTypeName context expectedType

getExpectedTypeName ::
  Context v ->
  Domain.Type ->
  M (Maybe (Either Meta.Index Name.Qualified))
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
    Domain.Glued _ _ value ->
      getExpectedTypeName context value
    Domain.Lazy lazyValue -> do
      value <- force lazyValue
      getExpectedTypeName context value
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

inferAndInsertMetas ::
  Context v ->
  InsertUntil ->
  Surface.Term ->
  M (Maybe (Either Meta.Index Name.Qualified)) ->
  M (Syntax.Term v, Domain.Type)
inferAndInsertMetas context until term@(Surface.Term span _) expectedTypeName = do
  Inferred term' type_ <- infer context term expectedTypeName
  (args, type') <- insertMetasReturningSyntax context until type_
  pure (Syntax.Spanned span $ Syntax.apps term' args, type')

insertMetasReturningSyntax ::
  Context v ->
  InsertUntil ->
  Domain.Type ->
  M ([(Plicity, Syntax.Term v)], Domain.Type)
insertMetasReturningSyntax context until type_ = do
  (args, res) <- insertMetas context until type_
  args' <- mapM (mapM $ readback context) args
  pure (args', res)

insertMetas ::
  Context v ->
  InsertUntil ->
  Domain.Type ->
  M ([(Plicity, Domain.Value)], Domain.Type)
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
          let value =
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
          let value =
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

isSubtype ::
  Context v ->
  Domain.Type ->
  Domain.Type ->
  M Bool
isSubtype context type1 type2 = do
  type2' <- Context.forceHead context type2
  case type2' of
    Domain.Pi binding domain plicity targetClosure
      | isImplicitish plicity ->
        do
          let name =
                Binding.toName binding
          (context', var) <- Context.extend context name domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          isSubtype context' type1 target
    _ -> do
      (_, type1') <- insertMetasReturningSyntax context UntilExplicit type1
      Context.try_ context $ Unification.unify context Flexibility.Rigid type1' type2

-------------------------------------------------------------------------------
-- Meta solutions

checkMetaSolutions ::
  Context Void ->
  Meta.EagerState ->
  M Syntax.MetaSolutions
checkMetaSolutions context metaVars =
  flip IntMap.traverseWithKey (Meta.eagerEntries metaVars) $ \index entry ->
    case entry of
      Meta.EagerUnsolved type_ _ _ span -> do
        ptype <- Context.toPrettyableClosedTerm context type_
        Context.report (Context.spanned span context) $
          Error.UnsolvedMetaVariable index ptype
        type' <- evaluate (Context.emptyFrom context) type_
        failTerm <- addLambdas (Context.emptyFrom context) type'
        pure (failTerm, type_, Meta.termMetas failTerm)
      Meta.EagerSolved solution metas type_ ->
        pure (solution, type_, Meta.direct metas)
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
          let name =
                Binding.toName binding
          domain' <- readback context' domain
          (context'', var) <- Context.extend context' name domain
          target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
          body <- addLambdas context'' target
          pure $ Syntax.Lam (Bindings.Unspanned name) domain' Explicit body
        _ ->
          readback context' $ Builtin.Unknown type_

-------------------------------------------------------------------------------

evaluate ::
  Context v ->
  Syntax.Term v ->
  M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEnvironment context)

lazyEvaluate ::
  Context v ->
  Syntax.Term v ->
  M Domain.Value
lazyEvaluate context =
  Evaluation.lazyEvaluate (Context.toEnvironment context)

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
