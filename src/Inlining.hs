{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Inlining where

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Syntax as Syntax
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import qualified Index
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import Protolude hiding (IntMap, Type, empty, evaluate)
import qualified Span
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

inlineDefinition :: Syntax.Definition -> M Syntax.Definition
inlineDefinition def = do
  let env = Environment.empty
  case def of
    Syntax.TypeDeclaration type_ ->
      Syntax.TypeDeclaration <$> inlineTerm env type_
    Syntax.ConstantDefinition term ->
      Syntax.ConstantDefinition <$> inlineTerm env term
    Syntax.DataDefinition boxity tele ->
      Syntax.DataDefinition boxity <$> inlineDataDefinition env tele

inlineDataDefinition
  :: Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v)
inlineDataDefinition env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) -> do
      constrDefs' <- OrderedHashMap.forMUnordered constrDefs $ inlineTerm env
      pure $ Telescope.Empty $ Syntax.ConstructorDefinitions constrDefs'
    Telescope.Extend name type_ plicity tele' -> do
      type' <- inlineTerm env type_
      (env', _) <- Environment.extend env
      tele'' <- inlineDataDefinition env' tele'
      pure $ Telescope.Extend name type' plicity tele''

inlineTerm :: Environment v -> Syntax.Term v -> M (Syntax.Term v)
inlineTerm env term = do
  value <- evaluate duplicable env term
  pure $
    readback
      Environment.Environment
        { indices = Environment.indices env
        , values = mempty
        , glueableBefore = Environment.glueableBefore env
        }
      value

-------------------------------------------------------------------------------

data Value
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index
  | Lets !Lets
  | Pi !Binding !Var !Type !Plicity !Type
  | Fun !Type !Plicity !Type
  | Lam !Bindings !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value !Type Branches !(Maybe Value)
  | Spanned !Span.Relative !Value
  deriving (Show)

type Environment = Environment.Environment Value

data Lets
  = LetType !Binding !Var !Type !Lets
  | Let !Bindings !Var !Value !Lets
  | In !Value
  deriving (Show)

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([Span.Relative], ([(Bindings, Var, Type, Plicity)], Value)))
  | LiteralBranches (OrderedHashMap Literal ([Span.Relative], Value))
  deriving (Show)

type Type = Value

-------------------------------------------------------------------------------

type Duplicable = forall v. Syntax.Term (Index.Succ v) -> Maybe (Syntax.Term v)

evaluate :: Duplicable -> Environment v -> Syntax.Term v -> M Value
evaluate dup env term =
  case term of
    Syntax.Var index -> do
      let var =
            Environment.lookupIndexVar index env
      case Environment.lookupVarValue var env of
        Nothing ->
          pure $ Var var
        Just value ->
          pure value
    Syntax.Global global ->
      pure $ Global global
    Syntax.Con con ->
      pure $ Con con
    Syntax.Lit lit ->
      pure $ Lit lit
    Syntax.Meta meta ->
      pure $ Meta meta
    Syntax.PostponedCheck {} ->
      panic "Inlining: Can't handle postponed check"
    Syntax.Lets lets -> do
      lets' <- evaluateLets dup env lets
      case lets' of
        In value ->
          pure value
        _ ->
          pure $ Lets lets'
    Syntax.Pi name domain plicity target -> do
      (env', var) <- Environment.extend env
      Pi name var
        <$> evaluate dup env domain
        <*> pure plicity
        <*> evaluate dup env' target
    Syntax.Fun domain plicity target ->
      Fun <$> evaluate dup env domain <*> pure plicity <*> evaluate dup env target
    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Environment.extend env
      Lam name var
        <$> evaluate dup env type_
        <*> pure plicity
        <*> evaluate dup env' body
    Syntax.App fun plicity arg ->
      App <$> evaluate dup env fun <*> pure plicity <*> evaluate dup env arg
    Syntax.Case scrutinee type_ branches defaultBranch ->
      -- TODO choose branch if variable is inlined to constructor
      Case
        <$> evaluate dup env scrutinee
        <*> evaluate dup env type_
        <*> evaluateBranches dup env branches
        <*> mapM (evaluate dup env) defaultBranch
    Syntax.Spanned span term' ->
      Spanned span <$> evaluate dup env term'

evaluateLets
  :: Duplicable
  -> Environment v
  -> Syntax.Lets v
  -> M Lets
evaluateLets dup env lets =
  case lets of
    Syntax.LetType _ _ (Syntax.Let _ Index.Zero term lets')
      | Just term' <- dup term -> do
          value <- evaluate dup env term'
          (env', _) <- Environment.extendValue env value
          evaluateLets dup env' lets'
    Syntax.LetType name type_ lets' -> do
      (env', var) <- Environment.extend env
      LetType name var <$> evaluate dup env type_ <*> evaluateLets dup env' lets'
    Syntax.Let name index term' lets' -> do
      let var =
            Environment.lookupIndexVar index env
      Let name var
        <$> evaluate dup env term'
        <*> evaluateLets dup env lets'
    Syntax.In term ->
      In <$> evaluate dup env term

evaluateBranches
  :: Duplicable
  -> Environment v
  -> Syntax.Branches v
  -> M Branches
evaluateBranches dup env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (mapM $ evaluateTelescope dup env) constructorBranches
    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> OrderedHashMap.mapMUnordered (mapM $ evaluate dup env) literalBranches

evaluateTelescope
  :: Duplicable
  -> Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M ([(Bindings, Var, Type, Plicity)], Value)
evaluateTelescope dup env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate dup env body
      pure ([], body')
    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate dup env type_
      (env', var) <- Environment.extend env
      (bindings, body) <- evaluateTelescope dup env' tele'
      pure ((name, var, type', plicity) : bindings, body)

readback :: Environment v -> Value -> Syntax.Term v
readback env value =
  case value of
    Var var ->
      case Environment.lookupVarIndex var env of
        Just i ->
          Syntax.Var i
        Nothing ->
          panic "Inlining.readback: scoping error"
    Global global ->
      Syntax.Global global
    Con con ->
      Syntax.Con con
    Lit lit ->
      Syntax.Lit lit
    Meta meta ->
      Syntax.Meta meta
    Lets lets ->
      Syntax.Lets $ readbackLets env lets
    Pi name var domain plicity target -> do
      let env' =
            Environment.extendVar env var
      Syntax.Pi name (readback env domain) plicity (readback env' target)
    Fun domain plicity target ->
      Syntax.Fun (readback env domain) plicity (readback env target)
    Lam name var type_ plicity body -> do
      let env' =
            Environment.extendVar env var
      Syntax.Lam name (readback env type_) plicity (readback env' body)
    App fun plicity arg ->
      Syntax.App (readback env fun) plicity (readback env arg)
    Case scrutinee type_ branches defaultBranch ->
      Syntax.Case
        (readback env scrutinee)
        (readback env type_)
        (readbackBranches env branches)
        (map (readback env) defaultBranch)
    Spanned span value' ->
      Syntax.Spanned span (readback env value')

readbackLets :: Environment v -> Lets -> Syntax.Lets v
readbackLets env lets =
  case lets of
    LetType name var type_ lets' -> do
      let env' =
            Environment.extendVar env var
      Syntax.LetType name (readback env type_) (readbackLets env' lets')
    Let name var term lets' ->
      Syntax.Let
        name
        (fromMaybe (panic "Inlining: indexless let") $ Environment.lookupVarIndex var env)
        (readback env term)
        (readbackLets env lets')
    In term ->
      Syntax.In $ readback env term

readbackBranches
  :: Environment v
  -> Branches
  -> Syntax.Branches v
readbackBranches env branches =
  case branches of
    ConstructorBranches constructorTypeName constructorBranches ->
      Syntax.ConstructorBranches constructorTypeName $
        map (uncurry $ readbackTelescope env) <$> constructorBranches
    LiteralBranches literalBranches ->
      Syntax.LiteralBranches $
        map (readback env) <$> literalBranches

readbackTelescope
  :: Environment v
  -> [(Bindings, Var, Type, Plicity)]
  -> Value
  -> Telescope Bindings Syntax.Type Syntax.Term v
readbackTelescope env bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env body
    (name, var, type_, plicity) : bindings' -> do
      let env' =
            Environment.extendVar env var
      Telescope.Extend name (readback env type_) plicity (readbackTelescope env' bindings' body)

duplicable :: Syntax.Term (Index.Succ v) -> Maybe (Syntax.Term v)
duplicable term =
  case term of
    Syntax.Var (Index.Succ index) ->
      Just $ Syntax.Var index
    Syntax.Var Index.Zero ->
      Nothing
    Syntax.Global global ->
      Just $ Syntax.Global global
    Syntax.Con con ->
      Just $ Syntax.Con con
    Syntax.Lit lit ->
      Just $ Syntax.Lit lit
    Syntax.Meta meta ->
      Just $ Syntax.Meta meta
    Syntax.PostponedCheck {} ->
      Nothing
    Syntax.Lets {} ->
      Nothing
    Syntax.Pi {} ->
      Nothing
    Syntax.Fun {} ->
      Nothing
    Syntax.Lam {} ->
      Nothing
    Syntax.App {} ->
      Nothing
    Syntax.Case {} ->
      Nothing
    Syntax.Spanned _ term' ->
      duplicable term'
