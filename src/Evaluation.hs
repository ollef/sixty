{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (Seq, force, evaluate)

import Rock

import qualified Domain
import Monad
import qualified Query
import qualified Syntax
import qualified Data.Tsil as Tsil

evaluate :: Domain.Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var v ->
      force $ Domain.lookupValue v env

    Syntax.Meta i ->
      pure $ Domain.meta i

    Syntax.Global name -> do
      maybeDefinition <- fetch $ Query.ElaboratedDefinition name
      case maybeDefinition of
        Just (term', _) ->
          evaluate Domain.empty term'

        Nothing ->
          pure $ Domain.global name

    Syntax.Let _ t _ s -> do
      t' <- lazy $ evaluate env t
      env' <- Domain.extendValue env t'
      evaluate env' s

    Syntax.Pi n t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Pi n t' (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ evaluate env t1
      t2' <- lazy $ evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam n t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Lam n t' (Domain.Closure env s)

    Syntax.App t1 t2 -> do
      t1' <- evaluate env t1
      t2' <- lazy $ evaluate env t2
      apply t1' t2'

apply :: Domain.Value -> Lazy Domain.Value -> M Domain.Value
apply fun arg =
  case fun of
    Domain.Lam _ _ closure ->
      evaluateClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (args Tsil.:> arg)

    _ ->
      panic "applying non-function"

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine = foldM apply

evaluateClosure :: Domain.Closure -> Lazy Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env body) argument = do
  env' <- Domain.extendValue env argument
  evaluate env' body
