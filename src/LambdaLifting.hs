{-# language OverloadedStrings #-}

module LambdaLifting where

import Protolude hiding (Type, IntSet, IntMap, evaluate, state)

import Data.Graph (SCC(AcyclicSCC))
import Data.HashMap.Lazy (HashMap)
import Rock

import Binding (Binding)
import qualified Binding
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Environment
import qualified Evaluation
import Extra (topoSortWith)
import qualified Index
import qualified LambdaLifted.Syntax as LambdaLifted
import Literal (Literal)
import Monad
import qualified Name
import Plicity
import qualified Query
import qualified Readback
import qualified Scope
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)
import qualified Var

liftDefinition
  :: Name.Qualified
  -> Syntax.Definition
  -> M (LambdaLifted.Definition, IntMap Int (Telescope LambdaLifted.Type LambdaLifted.Term Void))
liftDefinition name def = do
  let
    env =
      Environment.empty $ Scope.KeyedName Scope.Definition name
  case def of
    Syntax.TypeDeclaration {} ->
      panic "lifting type declaration"

    Syntax.ConstantDefinition term -> do
      ((vars, def'), state) <- runStateT (liftLambda env term) emptyState
      unless (null vars) $
        panic "lift definition: non-closed constant definition"

      pure (LambdaLifted.ConstantDefinition def', _liftedDefinitions state)

    Syntax.DataDefinition _ tele -> do
      (tele', state) <- runStateT (liftDataDefinition env tele) emptyState
      pure (LambdaLifted.DataDefinition tele', _liftedDefinitions state)

-------------------------------------------------------------------------------

data Value = Value !InnerValue Occurrences
  deriving Show

data InnerValue
  = Var !Var
  | Global !Name.Lifted
  | Con !Name.QualifiedConstructor [Value]
  | Lit !Literal
  | Let !Binding !Var !Value !Type !Value
  | Pi !Binding !Var !Type !Type
  | App !Value !Value
  | Case !Value !Branches !(Maybe Value)
  deriving Show

type Type = Value

data Branches
  = ConstructorBranches (HashMap Name.QualifiedConstructor ([(Binding, Var, Type)], Value))
  | LiteralBranches (HashMap Literal Value)
  deriving Show

type Occurrences = IntSet Var

occurrences :: Value -> Occurrences
occurrences (Value _ occs) =
  occs

makeVar :: Environment v -> Var -> Value
makeVar env var =
  Value (Var var) $
    IntSet.singleton var <>
    foldMap occurrences (Environment.lookupVarValue var env)

makeGlobal :: Name.Lifted -> Value
makeGlobal global =
  Value (Global global) mempty

makeCon :: Name.QualifiedConstructor -> [Value] -> Value
makeCon con args =
  Value (Con con args) $ foldMap occurrences args

makeLit :: Literal -> Value
makeLit lit =
  Value (Lit lit) mempty

makeLet :: Binding -> Var -> Value -> Type -> Value -> Value
makeLet binding var value type_ body =
  Value (Let binding var value type_ body) $
    occurrences value <>
    occurrences type_ <>
    IntSet.delete var (occurrences body)

makePi :: Binding -> Var -> Type -> Value -> Value
makePi name var domain target =
  Value (Pi name var domain target) $
    occurrences domain <>
    IntSet.delete var (occurrences target)

makeApp :: Value -> Value -> Value
makeApp fun arg =
  Value (App fun arg) $
    occurrences fun <>
    occurrences arg

makeApps :: Foldable f => Value -> f Value -> Value
makeApps =
  foldl makeApp

makeCase :: Value -> Branches -> Maybe Value -> Value
makeCase scrutinee branches defaultBranch =
  Value (Case scrutinee branches defaultBranch) $
    occurrences scrutinee <>
    branchOccurrences branches <>
    foldMap occurrences defaultBranch

branchOccurrences :: Branches -> Occurrences
branchOccurrences branches =
  case branches of
    ConstructorBranches constructorBranches ->
      foldMap (uncurry telescopeOccurrences) constructorBranches

    LiteralBranches literalBranches ->
      foldMap occurrences literalBranches

telescopeOccurrences :: [(Binding, Var, Type)] -> Value -> Occurrences
telescopeOccurrences tele body =
  case tele of
    [] ->
      occurrences body

    (_, var, type_):tele' ->
      occurrences type_ <>
      IntSet.delete var (telescopeOccurrences tele' body)

-------------------------------------------------------------------------------

data LiftState = LiftState
  { _nextIndex :: !Int
  , _liftedDefinitions :: IntMap Int (Telescope LambdaLifted.Type LambdaLifted.Term Void)
  } deriving Show

emptyState :: LiftState
emptyState =
  LiftState
    { _nextIndex = 1
    , _liftedDefinitions = mempty
    }

type Lift = StateT LiftState M

type Environment = Environment.Environment Value

extend :: Environment v -> Type -> Lift (Environment (Index.Succ v), Var)
extend env type_ =
  lift $ Environment.extendValue env type_

-------------------------------------------------------------------------------

evaluate :: Environment v -> Syntax.Term v -> [(Plicity, Syntax.Term v)] -> Lift Value
evaluate env term args =
  case term of
    Syntax.Var index ->
      applyArgs $ pure $ makeVar env $ Environment.lookupIndexVar index env

    Syntax.Global global ->
      applyArgs $ pure $ makeGlobal $ Name.Lifted global 0

    Syntax.Con con -> do
      term' <- lift $ saturatedConstructorApp env con args
      evaluate env term' []

    Syntax.Lit lit ->
      pure $ makeLit lit

    Syntax.Meta _ ->
      panic "LambdaLifting.evaluate meta"

    Syntax.Let name value type_ body ->
      applyArgs $ do
        type' <- evaluate env type_ []
        (env', var) <- extend env type'
        makeLet name var <$>
          evaluate env value [] <*>
          pure type' <*>
          evaluate env' body []

    Syntax.Pi name domain _plicity target -> do
      domain' <- evaluate env domain []
      (env', var) <- extend env domain'
      makePi name var domain' <$>
        evaluate env' target []

    Syntax.Fun domain _plicity target -> do
      var <- lift freshVar
      makePi "x" var <$>
        evaluate env domain [] <*>
        evaluate env target []

    Syntax.Lam {} -> do
      (argVars, def) <- liftLambda env term
      i <- gets _nextIndex

      let
        Scope.KeyedName _ name =
          Environment.scopeKey env

        liftedName =
          Name.Lifted name i

      modify $ \s -> s
        { _nextIndex = i + 1
        , _liftedDefinitions = IntMap.insert i def $ _liftedDefinitions s
        }
      pure $ makeApps (makeGlobal liftedName) $ makeVar env <$> argVars

    Syntax.App function _plicity argument ->
      makeApp <$>
        evaluate env function args <*>
        evaluate env argument []

    Syntax.Case scrutinee branches defaultBranch ->
      applyArgs $
        makeCase <$>
          evaluate env scrutinee [] <*>
          evaluateBranches env branches <*>
          mapM (\branch -> evaluate env branch []) defaultBranch

    Syntax.Spanned _ term' ->
      evaluate env term' args
  where
    applyArgs mresult = do
      args' <- mapM (\(_, term') -> evaluate env term' []) args
      result <- mresult
      pure $ makeApps result args'

saturatedConstructorApp
  :: Environment v
  -> Name.QualifiedConstructor
  -> [(Plicity, Syntax.Term v)]
  -> M (Syntax.Term v)
saturatedConstructorApp outerEnv con outerArgs = do
  constructorTele <- fetch $ Query.ConstructorType con
  let
    constructorType =
      Telescope.fold Syntax.Pi constructorTele

    env =
      outerEnv { Environment.values = mempty }

  argValues <- mapM (mapM $ Evaluation.evaluate env) outerArgs
  constructorTypeValue <-
    Evaluation.evaluate (Environment.empty $ Environment.scopeKey env) constructorType

  matchArguments env constructorTypeValue argValues Tsil.Empty
  where
    matchArguments
      :: Domain.Environment v
      -> Domain.Type
      -> [(Plicity, Domain.Value)]
      -> Domain.Spine
      -> M (Syntax.Term v)
    matchArguments env constructorType args resultSpine = do
      constructorType' <- Evaluation.forceHead env constructorType
      case (constructorType', args) of
        (Domain.Pi _ _ plicity1 targetClosure, (plicity2, arg):args')
          | plicity1 == plicity2 -> do
            target <- Evaluation.evaluateClosure targetClosure arg
            matchArguments env target args' $ resultSpine Tsil.:> (plicity2, arg)

        (Domain.Fun _ plicity1 target, (plicity2, arg):args')
          | plicity1 == plicity2 ->
            matchArguments env target args' $ resultSpine Tsil.:> (plicity2, arg)

        (_, []) ->
          makeLambdas env constructorType' resultSpine

        _ ->
          panic "saturatedConstructorApp plicity mismatch"

    makeLambdas
      :: Domain.Environment v
      -> Domain.Type
      -> Domain.Spine
      -> M (Syntax.Term v)
    makeLambdas env constructorType resultSpine = do
      constructorType' <- Evaluation.forceHead env constructorType
      case constructorType' of
        Domain.Pi name domain plicity targetClosure -> do
          (env', var) <- Environment.extend env
          let
            arg =
              Domain.var var
          target <- Evaluation.evaluateClosure targetClosure arg
          body <- makeLambdas env' target $ resultSpine Tsil.:> (plicity, arg)
          domain' <- Readback.readback env domain
          pure $ Syntax.Lam (Binding.Unspanned name) domain' plicity body

        Domain.Fun domain plicity target -> do
          (env', var) <- Environment.extend env
          body <- makeLambdas env' target $ resultSpine Tsil.:> (plicity, Domain.var var)
          domain' <- Readback.readback env domain
          pure $ Syntax.Lam "x" domain' plicity body

        _ ->
          Readback.readback env $ Domain.Neutral (Domain.Con con) resultSpine

evaluateBranches
  :: Environment v
  -> Syntax.Branches v
  -> Lift Branches
evaluateBranches env branches =
  case branches of
    Syntax.ConstructorBranches constructorBranches ->
      ConstructorBranches <$> mapM (evaluateTelescope env . snd) constructorBranches

    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> mapM (\(_, branch) -> evaluate env branch []) literalBranches

evaluateTelescope
  :: Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> Lift ([(Binding, Var, Type)], Value)
evaluateTelescope env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body []
      pure ([], body')

    Telescope.Extend name type_ _plicity tele' -> do
      type' <- evaluate env type_ []
      (env', var) <- extend env type'
      (bindings, body) <- evaluateTelescope env' tele'
      pure ((name, var, type'):bindings, body)

evaluateLambdaTelescope :: Environment v -> Syntax.Term v -> Lift ([(Binding, Var, Type)], Value)
evaluateLambdaTelescope env term =
  case term of
    Syntax.Lam name type_ _plicity body -> do
      type' <- evaluate env type_ []
      (env', var) <- extend env type'
      (tele, body') <- evaluateLambdaTelescope env' body
      pure ((name, var, type'):tele, body')

    Syntax.Spanned _ term' ->
      evaluateLambdaTelescope env term'

    _ -> do
      term' <- evaluate env term []
      pure ([], term')

liftLambda
  :: Environment v
  -> Syntax.Term v
  -> Lift ([Var], Telescope LambdaLifted.Type LambdaLifted.Term Void)
liftLambda env term = do
  (tele, body) <- evaluateLambdaTelescope env term

  let
    occs =
      telescopeOccurrences tele body

    sortedOccs =
      acyclic <$>
        topoSortWith
          identity
          (\var -> IntSet.toList $ foldMap occurrences $ Environment.lookupVarValue var env)
          (IntSet.toList occs)

    occurrenceTele =
      [ (Binding.Unspanned "x", var, type_)
      | var <- sortedOccs
      , let
          type_ =
            fromMaybe (panic "liftLambda no type") $ Environment.lookupVarValue var env
      ]

    emptyEnv =
      Environment.empty $ Environment.scopeKey env

  pure (sortedOccs, readbackTelescope emptyEnv (occurrenceTele <> tele) body)
  where
    acyclic :: SCC a -> a
    acyclic (AcyclicSCC a) = a
    acyclic _ = panic "liftLambda cyclic"

liftDataDefinition
  :: Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> Lift (Telescope LambdaLifted.Type LambdaLifted.ConstructorDefinitions v)
liftDataDefinition env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) -> do
      constrDefs' <- forM constrDefs $ \type_ -> do
        type' <- evaluate env type_ []
        pure $ readback env type'
      pure $ Telescope.Empty $ LambdaLifted.ConstructorDefinitions constrDefs'

    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate env type_ []
      (env', _) <- extend env type'
      tele'' <- liftDataDefinition env' tele'
      pure (Telescope.Extend name (readback env type') plicity tele'')

-------------------------------------------------------------------------------

readback :: Environment v -> Value -> LambdaLifted.Term v
readback env (Value value _) =
  case value of
    Var var ->
      LambdaLifted.Var $
        fromMaybe (panic "LambdaLifting.readback Var") $
          Environment.lookupVarIndex var env

    Global global ->
      LambdaLifted.Global global

    Con global args ->
      LambdaLifted.Con global $ readback env <$> args

    Lit lit ->
      LambdaLifted.Lit lit

    Let binding var value' type_ body ->
      LambdaLifted.Let
        (Binding.toName binding)
        (readback env value')
        (readback env type_)
        (readback (Environment.extendVar env var) body)

    Pi binding var domain target ->
      LambdaLifted.Pi
        (Binding.toName binding)
        (readback env domain)
        (readback (Environment.extendVar env var) target)

    App function argument ->
      LambdaLifted.App (readback env function) (readback env argument)

    Case scrutinee branches defaultBranch ->
      LambdaLifted.Case
        (readback env scrutinee)
        (readbackBranches env branches)
        (readback env <$> defaultBranch)

readbackBranches
  :: Environment v
  -> Branches
  -> LambdaLifted.Branches v
readbackBranches env branches =
  case branches of
    ConstructorBranches constructorBranches ->
      LambdaLifted.ConstructorBranches $ uncurry (readbackTelescope env) <$> constructorBranches

    LiteralBranches literalBranches ->
      LambdaLifted.LiteralBranches $ map (readback env) literalBranches

readbackTelescope
  :: Environment v
  -> [(Binding, Var, Type)]
  -> Value
  -> Telescope LambdaLifted.Type LambdaLifted.Term v
readbackTelescope env bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env body

    (name, var, type_):bindings' -> do
      let
        env' =
          Environment.extendVar env var
      Telescope.Extend name (readback env type_) Explicit (readbackTelescope env' bindings' body)
