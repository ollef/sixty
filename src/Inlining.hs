{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
module Inlining where

import Protolude hiding (Type, IntMap, evaluate, empty)

import Data.HashMap.Lazy (HashMap)

import qualified Environment
import qualified Meta
import Monad
import qualified Name
import Binding (Binding)
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

    Syntax.DataDefinition tele ->
      Syntax.DataDefinition <$> inlineDataDefinition env tele

inlineDataDefinition
  :: Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v)
inlineDataDefinition env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) -> do
      constrDefs' <- forM constrDefs $ inlineTerm env
      pure $ Telescope.Empty $ Syntax.ConstructorDefinitions constrDefs'

    Telescope.Extend name type_ plicity tele' -> do
      type' <- inlineTerm env type_
      (env', _) <- Environment.extend env
      tele'' <- inlineDataDefinition env' tele'
      pure $ Telescope.Extend name type' plicity tele''

inlineTerm :: Environment v -> Syntax.Term v -> M (Syntax.Term v)
inlineTerm env term = do
  value <- evaluate env term
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
  | Meta !Meta.Index
  | Let !Binding !Var !Value !Type !Value
  | Pi !Binding !Var !Type !Plicity !Type
  | Fun !Type !Plicity !Type
  | Lam !Binding !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value Branches !(Maybe Value)
  | Spanned !Span.Relative !Value
  deriving Show

type Environment = Environment.Environment Value

type Branches = HashMap Name.QualifiedConstructor ([Span.Relative], ([(Binding, Var, Type, Plicity)], Value))

type Type = Value

-------------------------------------------------------------------------------

evaluate :: Environment v -> Syntax.Term v -> M Value
evaluate env term =
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

    Syntax.Meta meta ->
      pure $ Meta meta

    Syntax.Let name term' type_ body
      | duplicable term' -> do
        value <- evaluate env term'
        env' <- Environment.extendValue env value
        evaluate env' body

      | otherwise -> do
        (env', var) <- Environment.extend env
        Let name var <$>
          evaluate env term' <*>
          evaluate env type_ <*>
          evaluate env' body

    Syntax.Pi name source plicity domain -> do
      (env', var) <- Environment.extend env
      Pi name var <$>
        evaluate env source <*>
        pure plicity <*>
        evaluate env' domain

    Syntax.Fun source plicity domain ->
      Fun <$> evaluate env source <*> pure plicity <*> evaluate env domain

    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Environment.extend env
      Lam name var <$>
        evaluate env type_ <*>
        pure plicity <*>
        evaluate env' body

    Syntax.App fun plicity arg ->
      App <$> evaluate env fun <*> pure plicity <*> evaluate env arg

    Syntax.Case scrutinee branches defaultBranch -> do
      scrutinee' <- evaluate env scrutinee
      -- TODO choose branch if variable is inlined to constructor
      Case scrutinee' <$>
        mapM (mapM $ evaluateBranch env) branches <*>
        mapM (evaluate env) defaultBranch

    Syntax.Spanned span term' ->
      Spanned span <$> evaluate env term'

evaluateBranch
  :: Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M ([(Binding, Var, Type, Plicity)], Value)
evaluateBranch env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body
      pure ([], body')

    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate env type_
      (env', var) <- Environment.extend env
      (bindings, body) <- evaluateBranch env' tele'
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

    Meta meta ->
      Syntax.Meta meta

    Let name var term type_ body -> do
      let
        env' =
          Environment.extendVar env var
      Syntax.Let name (readback env term) (readback env type_) (readback env' body)

    Pi name var source plicity domain -> do
      let
        env' =
          Environment.extendVar env var
      Syntax.Pi name (readback env source) plicity (readback env' domain)

    Fun source plicity domain ->
      Syntax.Fun (readback env source) plicity (readback env domain)

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
        (map (map $ uncurry $ readbackBranch env) branches)
        (map (readback env) defaultBranch)

    Spanned span value' ->
      Syntax.Spanned span (readback env value')

readbackBranch
  :: Environment v
  -> [(Binding, Var, Type, Plicity)]
  -> Value
  -> Telescope Syntax.Type Syntax.Term v
readbackBranch env bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env body

    (name, var, type_, plicity):bindings' -> do
      let
        env' =
          Environment.extendVar env var
      Telescope.Extend name (readback env type_) plicity (readbackBranch env' bindings' body)

duplicable :: Syntax.Term v -> Bool
duplicable term =
  case term of
    Syntax.Var {} ->
      True

    Syntax.Global {} ->
      True

    Syntax.Con {} ->
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
