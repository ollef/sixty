{-# language OverloadedStrings #-}

module LambdaLifting where

import Protolude hiding (Type, IntSet, IntMap, evaluate, state)

import Data.Graph (SCC(AcyclicSCC))
import Rock

import Binding (Binding)
import qualified Binding
import Bindings (Bindings)
import qualified Bindings
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Environment
import qualified Evaluation
import Extra (topoSortWith)
import qualified Index
import qualified LambdaLifted.Syntax as LambdaLifted
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Query
import qualified Readback
import qualified Scope
import qualified Core.Syntax as Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)
import qualified Var

liftDefinition
  :: Name.Qualified
  -> Syntax.Definition
  -> M (LambdaLifted.Definition, IntMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void))
liftDefinition name def = do
  let
    env =
      Environment.empty $ Scope.KeyedName Scope.Definition name
  case def of
    Syntax.TypeDeclaration type_ -> do
      let
        typeEnv =
          Environment.empty $ Scope.KeyedName Scope.Type name
      (type', state) <-
        runStateT
          (do
            type' <- evaluate typeEnv type_ []
            pure $ readback typeEnv type'
          )
          emptyState

      pure (LambdaLifted.TypeDeclaration type', _liftedDefinitions state)

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
  | Con !Name.QualifiedConstructor [Value] [Value]
  | Lit !Literal
  | Let !Name !Var !Value !Type !Value
  | Pi !Name !Var !Type !Type
  | App !Value !Value
  | Case !Value !Branches !(Maybe Value)
  deriving Show

type Type = Value

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([(Name, Var, Type)], Value))
  | LiteralBranches (OrderedHashMap Literal Value)
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

makeCon :: Name.QualifiedConstructor -> [Value] -> [Value] -> Value
makeCon con params args =
  Value (Con con params args) $
    foldMap occurrences params <>
    foldMap occurrences args

makeLit :: Literal -> Value
makeLit lit =
  Value (Lit lit) mempty

makeLet :: Name -> Var -> Value -> Type -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value <>
    occurrences type_ <>
    IntSet.delete var (occurrences body)

makePi :: Name -> Var -> Type -> Value -> Value
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
    ConstructorBranches _ constructorBranches ->
      foldMap (uncurry telescopeOccurrences) constructorBranches

    LiteralBranches literalBranches ->
      foldMap occurrences literalBranches

telescopeOccurrences :: [(Name, Var, Type)] -> Value -> Occurrences
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
  , _liftedDefinitions :: IntMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void)
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

    Syntax.Con con ->
      saturatedConstructorApp env con args

    Syntax.Lit lit ->
      pure $ makeLit lit

    Syntax.Meta _ ->
      panic "LambdaLifting.evaluate meta"

    Syntax.Let bindings value type_ body ->
      applyArgs $ do
        type' <- evaluate env type_ []
        (env', var) <- extend env type'
        makeLet (Bindings.toName bindings) var <$>
          evaluate env value [] <*>
          pure type' <*>
          evaluate env' body []

    Syntax.Pi binding domain _plicity target -> do
      domain' <- evaluate env domain []
      (env', var) <- extend env domain'
      makePi (Binding.toName binding) var domain' <$>
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
  -> Lift Value
saturatedConstructorApp env con args = do
  constructorTele <- fetch $ Query.ConstructorType con
  let
    constructorType =
      Telescope.fold Syntax.Pi constructorTele

    paramCount =
      Telescope.length constructorTele

    emptyEnv =
      Environment.emptyFrom env

  constructorTypeValue <- lift $ Evaluation.evaluate emptyEnv constructorType

  arity <- lift $ typeArity emptyEnv constructorTypeValue

  if length args < arity then do
    lambdas <- lift $ makeConstructorFunction con emptyEnv constructorTypeValue mempty
    evaluate env (Syntax.fromVoid lambdas) args

  else do
    args' <- mapM (\(_, arg) -> evaluate env arg []) args
    let
      (params, args'') =
        splitAt paramCount args'
    pure $ makeCon con params args''

makeConstructorFunction
  :: Name.QualifiedConstructor
  -> Domain.Environment v
  -> Domain.Type
  -> Domain.Spine
  -> M (Syntax.Term v)
makeConstructorFunction con env type_ spine = do
  type' <- Evaluation.forceHead env type_
  case type' of
    Domain.Pi binding domain plicity targetClosure -> do
      (env', var) <- Environment.extend env
      let
        arg =
          Domain.var var
      target <- Evaluation.evaluateClosure targetClosure arg
      body <- makeConstructorFunction con env' target $ spine Tsil.:> (plicity, arg)
      domain' <- Readback.readback env domain
      pure $ Syntax.Lam (Bindings.Unspanned $ Binding.toName binding) domain' plicity body

    Domain.Fun domain plicity target -> do
      (env', var) <- Environment.extend env
      body <- makeConstructorFunction con env' target $ spine Tsil.:> (plicity, Domain.var var)
      domain' <- Readback.readback env domain
      pure $ Syntax.Lam "x" domain' plicity body

    _ ->
      Readback.readback env $ Domain.Con con spine

typeArity
  :: Domain.Environment v
  -> Domain.Type
  -> M Int
typeArity env type_ = do
  type' <- Evaluation.forceHead env type_
  case type' of
    Domain.Pi _ _ _ targetClosure -> do
      (env', var) <- Environment.extend env
      target <- Evaluation.evaluateClosure targetClosure $ Domain.var var
      targetArity <- typeArity env' target
      pure $ targetArity + 1

    Domain.Fun _ _ target -> do
      targetArity <- typeArity env target
      pure $ targetArity + 1

    _ ->
      pure 0

evaluateBranches
  :: Environment v
  -> Syntax.Branches v
  -> Lift Branches
evaluateBranches env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (evaluateTelescope env . snd) constructorBranches

    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> OrderedHashMap.mapMUnordered (\(_, branch) -> evaluate env branch []) literalBranches

evaluateTelescope
  :: Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> Lift ([(Name, Var, Type)], Value)
evaluateTelescope env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body []
      pure ([], body')

    Telescope.Extend binding type_ _plicity tele' -> do
      type' <- evaluate env type_ []
      (env', var) <- extend env type'
      (bindings, body) <- evaluateTelescope env' tele'
      pure ((Bindings.toName binding, var, type'):bindings, body)

evaluateLambdaTelescope :: Environment v -> Syntax.Term v -> Lift ([(Name, Var, Type)], Value)
evaluateLambdaTelescope env term =
  case term of
    Syntax.Lam binding type_ _plicity body -> do
      type' <- evaluate env type_ []
      (env', var) <- extend env type'
      (tele, body') <- evaluateLambdaTelescope env' body
      pure ((Bindings.toName binding, var, type'):tele, body')

    Syntax.Spanned _ term' ->
      evaluateLambdaTelescope env term'

    _ -> do
      term' <- evaluate env term []
      pure ([], term')

liftLambda
  :: Environment v
  -> Syntax.Term v
  -> Lift ([Var], Telescope Name LambdaLifted.Type LambdaLifted.Term Void)
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
      [ ("x", var, type_)
      | var <- sortedOccs
      , let
          type_ =
            fromMaybe (panic "liftLambda no type") $ Environment.lookupVarValue var env
      ]

    emptyEnv =
      Environment.emptyFrom env

  pure (sortedOccs, readbackTelescope emptyEnv (occurrenceTele <> tele) body)
  where
    acyclic :: SCC a -> a
    acyclic (AcyclicSCC a) = a
    acyclic _ = panic "liftLambda cyclic"

liftDataDefinition
  :: Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> Lift (Telescope Name LambdaLifted.Type LambdaLifted.ConstructorDefinitions v)
liftDataDefinition env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) -> do
      constrDefs' <- OrderedHashMap.forMUnordered constrDefs $ \type_ -> do
        type' <- evaluate env type_ []
        pure $ readback env type'
      pure $ Telescope.Empty $ LambdaLifted.ConstructorDefinitions constrDefs'

    Telescope.Extend binding type_ plicity tele' -> do
      type' <- evaluate env type_ []
      (env', _) <- extend env type'
      tele'' <- liftDataDefinition env' tele'
      pure (Telescope.Extend (Binding.toName binding) (readback env type') plicity tele'')

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

    Con global params args ->
      LambdaLifted.Con global (readback env <$> params) (readback env <$> args)

    Lit lit ->
      LambdaLifted.Lit lit

    Let name var value' type_ body ->
      LambdaLifted.Let
        name
        (readback env value')
        (readback env type_)
        (readback (Environment.extendVar env var) body)

    Pi name var domain target ->
      LambdaLifted.Pi
        name
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
    ConstructorBranches constructorTypeName constructorBranches ->
      LambdaLifted.ConstructorBranches constructorTypeName $ uncurry (readbackTelescope env) <$> constructorBranches

    LiteralBranches literalBranches ->
      LambdaLifted.LiteralBranches $ map (readback env) literalBranches

readbackTelescope
  :: Environment v
  -> [(Name, Var, Type)]
  -> Value
  -> Telescope Name LambdaLifted.Type LambdaLifted.Term v
readbackTelescope env bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env body

    (name, var, type_):bindings' -> do
      let
        env' =
          Environment.extendVar env var
      Telescope.Extend name (readback env type_) Explicit (readbackTelescope env' bindings' body)
