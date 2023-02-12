{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module LambdaLifting where

import Core.Binding (Binding)
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import Data.Graph (SCC (AcyclicSCC))
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Extra (topoSortWith)
import qualified Index
import qualified LambdaLifted.Syntax as LambdaLifted
import Literal (Literal)
import Monad
import Name (Name)
import qualified Name
import Plicity
import Protolude hiding (Type, evaluate, state)
import qualified Query
import Rock
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

liftDefinition
  :: Name.Qualified
  -> Syntax.Definition
  -> M (LambdaLifted.Definition, EnumMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void))
liftDefinition name def = do
  let env = Environment.empty
  case def of
    Syntax.TypeDeclaration type_ -> do
      (type', state) <-
        runStateT
          ( do
              type' <- evaluate name env type_ []
              pure $ readback env type'
          )
          emptyState

      pure (LambdaLifted.TypeDeclaration type', state.liftedDefinitions)
    Syntax.ConstantDefinition term -> do
      ((vars, def'), state) <- runStateT (liftLambda name env term) emptyState
      unless (null vars) $
        panic "lift definition: non-closed constant definition"

      pure (LambdaLifted.ConstantDefinition def', state.liftedDefinitions)
    Syntax.DataDefinition boxity tele -> do
      (tele', state) <- runStateT (liftDataDefinition name env tele) emptyState
      pure (LambdaLifted.DataDefinition boxity tele', state.liftedDefinitions)

-------------------------------------------------------------------------------

data Value = Value !InnerValue Occurrences
  deriving (Show)

data InnerValue
  = Var !Var
  | Global !Name.Lifted
  | Con !Name.QualifiedConstructor [Value] [Value]
  | Lit !Literal
  | Let !Name !Var !Value !Type !Value
  | Pi !Name !Var !Type !Type
  | App !Value !Value
  | Case !Value !Branches !(Maybe Value)
  deriving (Show)

type Type = Value

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([(Name, Var, Type)], Value))
  | LiteralBranches (OrderedHashMap Literal Value)
  deriving (Show)

type Occurrences = EnumSet Var

occurrences :: Value -> Occurrences
occurrences (Value _ occs) =
  occs

makeVar :: Environment v -> Var -> Value
makeVar env var =
  Value (Var var) $
    EnumSet.singleton var
      <> foldMap (occurrences . snd) (Environment.lookupVarValue var env)

makeGlobal :: Name.Lifted -> Value
makeGlobal global =
  Value (Global global) mempty

makeCon :: Name.QualifiedConstructor -> [Value] -> [Value] -> Value
makeCon con params args =
  Value (Con con params args) $
    foldMap occurrences params
      <> foldMap occurrences args

makeLit :: Literal -> Value
makeLit lit =
  Value (Lit lit) mempty

makeLet :: Name -> Var -> Value -> Type -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value
      <> occurrences type_
      <> EnumSet.delete var (occurrences body)

makePi :: Name -> Var -> Type -> Value -> Value
makePi name var domain target =
  Value (Pi name var domain target) $
    occurrences domain
      <> EnumSet.delete var (occurrences target)

makeApp :: Value -> Value -> Value
makeApp fun arg =
  Value (App fun arg) $
    occurrences fun
      <> occurrences arg

makeApps :: Foldable f => Value -> f Value -> Value
makeApps =
  foldl makeApp

makeCase :: Value -> Branches -> Maybe Value -> Value
makeCase scrutinee branches defaultBranch =
  Value (Case scrutinee branches defaultBranch) $
    occurrences scrutinee
      <> branchOccurrences branches
      <> foldMap occurrences defaultBranch

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
    (_, var, type_) : tele' ->
      occurrences type_
        <> EnumSet.delete var (telescopeOccurrences tele' body)

-------------------------------------------------------------------------------

data LiftState = LiftState
  { nextIndex :: !Int
  , liftedDefinitions :: EnumMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void)
  }
  deriving (Show)

emptyState :: LiftState
emptyState =
  LiftState
    { nextIndex = 1
    , liftedDefinitions = mempty
    }

type Lift = StateT LiftState M

type Environment = Environment.Environment (Maybe Value, Type)

extend :: Environment v -> Type -> Lift (Environment (Index.Succ v), Var)
extend env type_ =
  lift $ Environment.extendValue env (Nothing, type_)

extendValue :: Environment v -> Value -> Type -> Lift (Environment (Index.Succ v), Var)
extendValue env value type_ =
  lift $ Environment.extendValue env (Just value, type_)

-------------------------------------------------------------------------------

evaluate
  :: Name.Qualified
  -> Environment v
  -> Syntax.Term v
  -> [(Plicity, Syntax.Term v)]
  -> Lift Value
evaluate baseName env term args =
  case term of
    Syntax.Var index -> do
      let var =
            Environment.lookupIndexVar index env
      applyArgs $
        case Environment.lookupVarValue var env of
          Just (Just value, _) ->
            pure value
          _ ->
            pure $ makeVar env $ Environment.lookupIndexVar index env
    Syntax.Global global ->
      applyArgs $ pure $ makeGlobal $ Name.Lifted global 0
    Syntax.Con con ->
      saturatedConstructorApp baseName env con args
    Syntax.Lit lit ->
      pure $ makeLit lit
    Syntax.Meta _ ->
      panic "LambdaLifting.evaluate meta"
    Syntax.PostponedCheck {} ->
      panic "LambdaLifting.evaluate postponed check"
    Syntax.Lets lets ->
      applyArgs $
        evaluateLets baseName env lets
    Syntax.Pi binding domain _plicity target -> do
      domain' <- evaluate baseName env domain []
      (env', var) <- extend env domain'
      makePi (Binding.toName binding) var domain'
        <$> evaluate baseName env' target []
    Syntax.Fun domain _plicity target -> do
      var <- lift freshVar
      makePi "x" var
        <$> evaluate baseName env domain []
        <*> evaluate baseName env target []
    Syntax.Lam {} -> do
      (argVars, def) <- liftLambda baseName env term
      i <- gets (.nextIndex)

      let liftedName =
            Name.Lifted baseName i

      modify $ \s ->
        s
          { nextIndex = i + 1
          , liftedDefinitions = EnumMap.insert i def s.liftedDefinitions
          }
      pure $ makeApps (makeGlobal liftedName) $ makeVar env <$> argVars
    Syntax.App function plicity argument ->
      evaluate baseName env function ((plicity, argument) : args)
    Syntax.Case scrutinee branches defaultBranch ->
      applyArgs $
        makeCase
          <$> evaluate baseName env scrutinee []
          <*> evaluateBranches baseName env branches
          <*> mapM (\branch -> evaluate baseName env branch []) defaultBranch
    Syntax.Spanned _ term' ->
      evaluate baseName env term' args
  where
    applyArgs mresult = do
      args' <- mapM (\(_, term') -> evaluate baseName env term' []) args
      result <- mresult
      pure $ makeApps result args'

evaluateLets :: Name.Qualified -> Environment v -> Syntax.Lets v -> Lift Value
evaluateLets baseName env lets =
  case lets of
    Syntax.LetType _binding type_ (Syntax.Let bindings Index.Zero term lets') -> do
      type' <- evaluate baseName env type_ []
      (env', var) <- extend env type'
      makeLet (Bindings.toName bindings) var
        <$> evaluate baseName env' term []
        <*> pure type'
        <*> evaluateLets baseName env' lets'
    Syntax.In body ->
      evaluate baseName env body []
    _ ->
      panic "TODO lambda lifting mutually recursive lets not yet supported"

-- - Sort definitions by dependency
-- - Make values in recursive groups functions from unit
-- - Lambda lift

saturatedConstructorApp
  :: Name.Qualified
  -> Environment v
  -> Name.QualifiedConstructor
  -> [(Plicity, Syntax.Term v)]
  -> Lift Value
saturatedConstructorApp baseName env con args = do
  constructorTele <- fetch $ Query.ConstructorType con
  let constructorType =
        Telescope.fold Syntax.Pi constructorTele

      paramCount =
        Telescope.length constructorTele

      emptyEnv =
        Environment.empty

  constructorTypeValue <- lift $ Evaluation.evaluate emptyEnv constructorType

  arity <- lift $ typeArity emptyEnv constructorTypeValue

  if length args < arity
    then do
      lambdas <- lift $ makeConstructorFunction con emptyEnv constructorTypeValue mempty
      evaluate baseName env (Syntax.fromVoid lambdas) args
    else do
      args' <- mapM (\(_, arg) -> evaluate baseName env arg []) args
      let (params, args'') =
            splitAt paramCount args'
      pure $ makeCon con params args''

makeConstructorFunction
  :: Name.QualifiedConstructor
  -> Domain.Environment v
  -> Domain.Type
  -> Tsil (Plicity, Domain.Value)
  -> M (Syntax.Term v)
makeConstructorFunction con env type_ spine = do
  type' <- Evaluation.forceHead env type_
  case type' of
    Domain.Pi binding domain plicity targetClosure -> do
      (env', var) <- Environment.extend env
      let arg =
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
  :: Name.Qualified
  -> Environment v
  -> Syntax.Branches v
  -> Lift Branches
evaluateBranches baseName env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (evaluateTelescope baseName env . snd) constructorBranches
    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> OrderedHashMap.mapMUnordered (\(_, branch) -> evaluate baseName env branch []) literalBranches

evaluateTelescope
  :: Name.Qualified
  -> Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> Lift ([(Name, Var, Type)], Value)
evaluateTelescope baseName env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate baseName env body []
      pure ([], body')
    Telescope.Extend binding type_ _plicity tele' -> do
      type' <- evaluate baseName env type_ []
      (env', var) <- extend env type'
      (bindings, body) <- evaluateTelescope baseName env' tele'
      pure ((Bindings.toName binding, var, type') : bindings, body)

evaluateLambdaTelescope
  :: Name.Qualified -> Environment v -> Syntax.Term v -> Lift ([(Name, Var, Type)], Value)
evaluateLambdaTelescope baseName env term =
  case term of
    Syntax.Lam binding type_ _plicity body -> do
      type' <- evaluate baseName env type_ []
      (env', var) <- extend env type'
      (tele, body') <- evaluateLambdaTelescope baseName env' body
      pure ((Bindings.toName binding, var, type') : tele, body')
    Syntax.Spanned _ term' ->
      evaluateLambdaTelescope baseName env term'
    _ -> do
      term' <- evaluate baseName env term []
      pure ([], term')

liftLambda
  :: Name.Qualified
  -> Environment v
  -> Syntax.Term v
  -> Lift ([Var], Telescope Name LambdaLifted.Type LambdaLifted.Term Void)
liftLambda baseName env term = do
  (tele, body) <- evaluateLambdaTelescope baseName env term

  let occs =
        telescopeOccurrences tele body

      sortedOccs =
        acyclic
          <$> topoSortWith
            identity
            (\var -> EnumSet.toList $ foldMap (occurrences . snd) $ Environment.lookupVarValue var env)
            (EnumSet.toList occs)

      occurrenceTele =
        [ ("x", var, type_)
        | var <- sortedOccs
        , let type_ =
                snd $ fromMaybe (panic "liftLambda no type") $ Environment.lookupVarValue var env
        ]

      emptyEnv =
        Environment.empty

  pure (sortedOccs, readbackTelescope emptyEnv (occurrenceTele <> tele) body)
  where
    acyclic :: SCC a -> a
    acyclic (AcyclicSCC a) = a
    acyclic _ = panic "liftLambda cyclic"

liftDataDefinition
  :: Name.Qualified
  -> Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> Lift (Telescope Name LambdaLifted.Type LambdaLifted.ConstructorDefinitions v)
liftDataDefinition baseName env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) -> do
      constrDefs' <- OrderedHashMap.forMUnordered constrDefs $ \type_ -> do
        type' <- evaluate baseName env type_ []
        pure $ readback env type'
      pure $ Telescope.Empty $ LambdaLifted.ConstructorDefinitions constrDefs'
    Telescope.Extend binding type_ plicity tele' -> do
      type' <- evaluate baseName env type_ []
      (env', _) <- extend env type'
      tele'' <- liftDataDefinition baseName env' tele'
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
    (name, var, type_) : bindings' -> do
      let env' =
            Environment.extendVar env var
      Telescope.Extend name (readback env type_) Explicit (readbackTelescope env' bindings' body)
