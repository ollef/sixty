{-# language OverloadedStrings #-}
module ClosureConverted.Evaluation where

import Protolude hiding (head, evaluate)

import Data.HashMap.Lazy as HashMap
import Rock

import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Syntax as Syntax
import qualified Environment
import Literal (Literal)
import Monad
import qualified Name
import qualified Query
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

evaluate :: Domain.Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var index -> do
      let
        var =
          Environment.lookupIndexVar index env
      pure $ Domain.var var

    Syntax.Global name -> do
      maybeDefinition <- fetchVisibleDefinition env name
      case maybeDefinition of
        Just (Syntax.ConstantDefinition term') -> do
          evaluate (Environment.empty $ Environment.scopeKey env) term'

        _ ->
          pure $ Domain.global name

    Syntax.Con con params args ->
      Domain.Con con <$> mapM (evaluate env) params <*> mapM (evaluate env) args

    Syntax.Lit lit ->
      pure $ Domain.Lit lit

    Syntax.Let _ term' _ body -> do
      term'' <- evaluate env term'
      (env', _) <- Environment.extendValue env term''
      evaluate env' body

    Syntax.Function tele ->
      pure $ Domain.Function tele

    Syntax.Apply name args -> do
      args' <- mapM (evaluate env) args
      maybeDefinition <- fetchVisibleDefinition env name
      case maybeDefinition of
        Just (Syntax.FunctionDefinition tele) -> do
          maybeResult <- apply env (Telescope.fromVoid tele) args'
          case maybeResult of
            Nothing ->
              panic "ClosureConverted.Evaluation: application arity mismatch"

            Just result ->
              pure result

        _ ->
          pure $ Domain.Neutral (Domain.Global name) args'

    Syntax.Pi name domain target -> do
      domain' <- evaluate env domain
      pure $ Domain.Pi name domain' $ Domain.Closure env target

    Syntax.Closure global args -> do
      args' <- mapM (evaluate env) args
      pure $ Domain.Neutral (Domain.Global global) args'

    Syntax.ApplyClosure fun args -> do
      fun' <- evaluate env fun
      args' <- mapM (evaluate env) args
      applyClosure env fun' args'

    Syntax.Case scrutinee branches defaultBranch -> do
      scrutineeValue <- evaluate env scrutinee
      case (scrutineeValue, branches) of
        (Domain.Con constr _params args, Syntax.ConstructorBranches constructorBranches) ->
          chooseConstructorBranch env constr args constructorBranches defaultBranch

        (Domain.Lit lit, Syntax.LiteralBranches literalBranches) ->
          chooseLiteralBranch env lit literalBranches defaultBranch

        _ ->
          pure $
            Domain.Neutral
            (Domain.Case scrutineeValue $ Domain.Branches env branches defaultBranch)
            mempty

chooseConstructorBranch
  :: Domain.Environment v
  -> Name.QualifiedConstructor
  -> [Domain.Value]
  -> Syntax.ConstructorBranches v
  -> Maybe (Syntax.Term v)
  -> M Domain.Value
chooseConstructorBranch outerEnv constr outerArgs branches defaultBranch =
  case (HashMap.lookup constr branches, defaultBranch) of
    (Nothing, Nothing) ->
      panic "chooseBranch no branches"

    (Nothing, Just branch) ->
      evaluate outerEnv branch

    (Just tele, _) ->
      go outerEnv outerArgs tele
  where
    go
      :: Domain.Environment v
      -> [Domain.Value]
      -> Telescope Syntax.Type Syntax.Term v
      -> M Domain.Value
    go env args tele =
      case (args, tele) of
        ([], Telescope.Empty branch) ->
          evaluate env branch

        (arg:args', Telescope.Extend _ _ _ target) -> do
          (env', _) <- Environment.extendValue env arg
          go env' args' target

        _ ->
          panic "chooseConstructorBranch mismatch"

chooseLiteralBranch
  :: Domain.Environment v
  -> Literal
  -> Syntax.LiteralBranches v
  -> Maybe (Syntax.Term v)
  -> M Domain.Value
chooseLiteralBranch outerEnv lit branches defaultBranch =
  case (HashMap.lookup lit branches, defaultBranch) of
    (Nothing, Nothing) ->
      panic "chooseLiteralBranch no branches"

    (Nothing, Just branch) ->
      evaluate outerEnv branch

    (Just branch, _) ->
      evaluate outerEnv branch

apply
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> [Domain.Value]
  -> M (Maybe Domain.Value)
apply env tele args =
  case (tele, args) of
    (Telescope.Empty body, _) -> do
      body' <- evaluate env body
      Just <$>
        case args of
          [] ->
            pure body'

          _ ->
            applyClosure env body' args

    (Telescope.Extend _ _ _ tele', arg:args') -> do
      (env', _) <- Environment.extendValue env arg
      apply env' tele' args'

    _ ->
      pure Nothing

applyClosure :: Domain.Environment v -> Domain.Value -> [Domain.Value] -> M Domain.Value
applyClosure env fun args =
  case fun of
    Domain.Neutral head preArgs -> do
      let
        args' =
          preArgs <> args

        neutral =
          Domain.Neutral head args'

      case head of
        Domain.Global global -> do
          maybeDefinition <- fetchVisibleDefinition env global
          case maybeDefinition of
            Just (Syntax.FunctionDefinition tele) -> do
              maybeResult <- apply env (Telescope.fromVoid tele) args'
              pure $
                case maybeResult of
                  Nothing ->
                    neutral

                  Just result ->
                    result

            _ ->
              pure neutral

        Domain.Var _ ->
          pure neutral

        Domain.Case {} ->
          pure neutral

    _ ->
      panic "ClosureConverted.Evaluation: applying non-neutral"

evaluateClosure :: Domain.Closure -> Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env body) argument = do
  (env', _) <- Environment.extendValue env argument
  evaluate env' body

fetchVisibleDefinition :: Domain.Environment v -> Name.Lifted -> M (Maybe Syntax.Definition)
fetchVisibleDefinition env name@(Name.Lifted baseName _) = do
  definitionVisible <- fetch $ Query.IsDefinitionVisible (Environment.scopeKey env) baseName
  if definitionVisible then do
    fetch $ Query.ClosureConverted name

  else
    pure Nothing
