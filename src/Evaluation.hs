{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (Seq, force, evaluate)

import Rock

import qualified Data.Tsil as Tsil
import qualified Domain
import Monad
import qualified Name
import Plicity
import qualified Query
import qualified Scope
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified Domain.Telescope as Domain (Telescope)
import qualified Domain.Telescope

evaluateConstructorDefinitions
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Domain.Telescope Domain.Type [(Name.Constructor, Domain.Type)])
evaluateConstructorDefinitions env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
      constrs' <- forM constrs $ \(constr, type_) -> do
        type' <- evaluate env type_
        pure (constr, type')
      pure $ Domain.Telescope.Empty constrs'

    Telescope.Extend name source plicity domain -> do
      source' <- evaluate env source
      pure $ Domain.Telescope.Extend name source' plicity $ \param -> do
        env' <- Domain.extendValue env param
        evaluateConstructorDefinitions env' domain

evaluate :: Domain.Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var index -> do
      let
        var =
          Domain.lookupVar index env

      pure $ Domain.Glued (Domain.Var var) mempty $ Domain.lookupValue var env

    Syntax.Global name -> do
      visibility <- fetch $ Query.Visibility (Domain.scopeKey env) name
      case visibility of
        Scope.Type ->
          pure $ Domain.global name

        Scope.Definition -> do
          maybeDefinition <- fetch $ Query.ElaboratedDefinition name
          case maybeDefinition of
            Just (Syntax.ConstantDefinition term', _) -> do
              value <- lazy $ evaluate (Domain.empty $ Domain.scopeKey env) term'
              pure $ Domain.Glued (Domain.Global name) mempty value

            _ ->
              pure $ Domain.global name

    Syntax.Con c ->
      pure $ Domain.con c

    Syntax.Meta i ->
      pure $ Domain.meta i

    Syntax.Let _ t _ s -> do
      t' <- lazy $ evaluate env t
      env' <- Domain.extendValue env t'
      evaluate env' s

    Syntax.Pi n t p s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Pi n t' p (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ evaluate env t1
      t2' <- lazy $ evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam n t p s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Lam n t' p (Domain.Closure env s)

    Syntax.App t1 p t2 -> do
      t1' <- evaluate env t1
      t2' <- lazy $ evaluate env t2
      apply t1' p t2'

    Syntax.Case scrutinee branches -> do
      scrutineeValue <- evaluate env scrutinee
      case scrutineeValue of
        Domain.Neutral (Domain.Con constr) spine ->
          chooseBranch env constr (toList spine) branches

        _ ->
          pure $ Domain.Case scrutineeValue $ Domain.Branches env branches

chooseBranch
  :: Domain.Environment v
  -> Name.QualifiedConstructor
  -> [(Plicity, Lazy Domain.Value)]
  -> [Syntax.Branch v]
  -> M Domain.Value
chooseBranch outerEnv constr outerArgs branches =
  go outerEnv outerArgs $
    case filter (\(Syntax.Branch c _)-> c == constr) branches of
      [] ->
        panic "chooseBranch no branches"

      Syntax.Branch _ tele:_ ->
        tele
  where
    go
      :: Domain.Environment v
      -> [(Plicity, Lazy Domain.Value)]
      -> Telescope Syntax.Type Syntax.Term v
      -> M Domain.Value
    go env args tele =
      case (args, tele) of
        ([], Telescope.Empty branch) ->
          evaluate env branch

        ((plicity1, arg):args', Telescope.Extend _ _ plicity2 domain)
          | plicity1 == plicity2 -> do
            env' <- Domain.extendValue env arg
            go env' args' domain

        _ ->
          panic "chooseBranch mismatch"

apply :: Domain.Value -> Plicity -> Lazy Domain.Value -> M Domain.Value
apply fun plicity arg =
  case fun of
    Domain.Lam _ _  plicity' closure
      | plicity == plicity' ->
      evaluateClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (args Tsil.:> (plicity, arg))

    Domain.Glued hd args value -> do
      appliedValue <- lazy $ do
        value' <- force value
        apply value' plicity arg
      pure $ Domain.Glued hd (args Tsil.:> (plicity, arg)) appliedValue

    _ ->
      panic "applying non-function"

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine = foldM (\val (plicity, arg) -> apply val plicity arg)

evaluateClosure :: Domain.Closure -> Lazy Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env body) argument = do
  env' <- Domain.extendValue env argument
  evaluate env' body
