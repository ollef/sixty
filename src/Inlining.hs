{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module Inlining where

import Protolude hiding (Type, IntMap, evaluate, empty)

import Binding (Binding)
import Bindings (Bindings)
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)

inlineDefinition :: Scope.KeyedName -> Syntax.Definition -> M Syntax.Definition
inlineDefinition scopeKey def = do
  let
    env =
      Environment.empty scopeKey
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
  pure $ readback
    Environment.Environment
      { scopeKey = Environment.scopeKey env
      , indices = Environment.indices env
      , values = mempty
      }
    value

-------------------------------------------------------------------------------

data Value
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index
  | Let !Bindings !Var !Value !Type !Value
  | Pi !Binding !Var !Type !Plicity !Type
  | Fun !Type !Plicity !Type
  | Lam !Bindings !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value Branches !(Maybe Value)
  | Spanned !Span.Relative !Value
  deriving Show

type Environment = Environment.Environment Value

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([Span.Relative], ([(Bindings, Var, Type, Plicity)], Value)))
  | LiteralBranches (OrderedHashMap Literal ([Span.Relative], Value))
  deriving Show

type Type = Value

-------------------------------------------------------------------------------

type Duplicable = forall v. Syntax.Term v -> Bool

evaluate :: Duplicable -> Environment v -> Syntax.Term v -> M Value
evaluate dup env term =
  case term of
    Syntax.Var index -> do
      let
        var =
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

    Syntax.Let name term' type_ body
      | duplicable term' -> do
        value <- evaluate dup env term'
        (env', _) <- Environment.extendValue env value
        evaluate dup env' body

      | otherwise -> do
        (env', var) <- Environment.extend env
        Let name var <$>
          evaluate dup env term' <*>
          evaluate dup env type_ <*>
          evaluate dup env' body

    Syntax.Pi name domain plicity target -> do
      (env', var) <- Environment.extend env
      Pi name var <$>
        evaluate dup env domain <*>
        pure plicity <*>
        evaluate dup env' target

    Syntax.Fun domain plicity target ->
      Fun <$> evaluate dup env domain <*> pure plicity <*> evaluate dup env target

    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Environment.extend env
      Lam name var <$>
        evaluate dup env type_ <*>
        pure plicity <*>
        evaluate dup env' body

    Syntax.App fun plicity arg ->
      App <$> evaluate dup env fun <*> pure plicity <*> evaluate dup env arg

    Syntax.Case scrutinee branches defaultBranch -> do
      scrutinee' <- evaluate dup env scrutinee
      -- TODO choose branch if variable is inlined to constructor
      Case scrutinee' <$>
        evaluateBranches dup env branches <*>
        mapM (evaluate dup env) defaultBranch

    Syntax.Spanned span term' ->
      Spanned span <$> evaluate dup env term'

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
      pure ((name, var, type', plicity):bindings, body)

readback :: Environment v -> Value -> Syntax.Term v
readback env value =
  case value of
    Var var ->
      case Environment.lookupVarIndex var env of
        Just i ->
          Syntax.Var i

        Nothing ->
          panic "Substitution.readback: scoping error"

    Global global ->
      Syntax.Global global

    Con con ->
      Syntax.Con con

    Lit lit ->
      Syntax.Lit lit

    Meta meta ->
      Syntax.Meta meta

    Let name var term type_ body -> do
      let
        env' =
          Environment.extendVar env var
      Syntax.Let name (readback env term) (readback env type_) (readback env' body)

    Pi name var domain plicity target -> do
      let
        env' =
          Environment.extendVar env var
      Syntax.Pi name (readback env domain) plicity (readback env' target)

    Fun domain plicity target ->
      Syntax.Fun (readback env domain) plicity (readback env target)

    Lam name var type_ plicity body -> do
      let
        env' =
          Environment.extendVar env var
      Syntax.Lam name (readback env type_) plicity (readback env' body)

    App fun plicity arg ->
      Syntax.App (readback env fun) plicity (readback env arg)

    Case scrutinee branches defaultBranch ->
      Syntax.Case
        (readback env scrutinee)
        (readbackBranches env branches)
        (map (readback env) defaultBranch)

    Spanned span value' ->
      Syntax.Spanned span (readback env value')

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

    (name, var, type_, plicity):bindings' -> do
      let
        env' =
          Environment.extendVar env var
      Telescope.Extend name (readback env type_) plicity (readbackTelescope env' bindings' body)

duplicable :: Syntax.Term v -> Bool
duplicable term =
  case term of
    Syntax.Var {} ->
      True

    Syntax.Global {} ->
      True

    Syntax.Con {} ->
      True

    Syntax.Lit {} ->
      True

    Syntax.Meta {} ->
      True

    Syntax.Let {} ->
      False

    Syntax.Pi {} ->
      False

    Syntax.Fun {} ->
      False

    Syntax.Lam {} ->
      False

    Syntax.App {} ->
      False

    Syntax.Case {} ->
      False

    Syntax.Spanned _ term' ->
      duplicable term'
