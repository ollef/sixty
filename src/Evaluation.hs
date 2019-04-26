{-# language OverloadedStrings #-}
module Evaluation where

import Protolude

import qualified Bound.Scope.Simple as Bound

import qualified Domain
import Monad
import qualified Syntax
import qualified Tsil

eval :: Syntax.Env (M Domain.Value) v -> Syntax.Term v -> M Domain.Value
eval env term =
  case term of
    Syntax.Var v ->
      Syntax.lookupValue env v

    Syntax.Global g ->
      pure $ Domain.global g -- TODO

    Syntax.Let t (Bound.Scope s) -> do
      t' <- lazy $ eval env t
      eval (Syntax.Snoc env t') s

    Syntax.Pi t s -> do
      t' <- lazy $ eval env t
      pure $ Domain.Pi t' (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ eval env t1
      t2' <- lazy $ eval env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam s ->
      pure $ Domain.Lam (Domain.Closure env s)

    Syntax.App t1 t2 -> do
      t1' <- eval env t1
      t2' <- lazy $ eval env t2
      apply t1' t2'

apply :: Domain.Value -> M Domain.Value -> M Domain.Value
apply fun arg =
  case fun of
    Domain.Lam closure ->
      evalClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (Tsil.Snoc args arg)

    _ ->
      panic "applying non-function"

evalClosure :: Domain.Closure -> M Domain.Value -> M Domain.Value
evalClosure (Domain.Closure env (Bound.Scope body)) x =
  eval (Syntax.Snoc env x) body

readBack :: Domain.Env v -> Domain.Value -> M (Syntax.Term v)
readBack env value =
  case value of
    Domain.Neutral hd spine ->
      readBackNeutral env hd spine

    Domain.Lam closure ->
      Syntax.Lam <$> readBackClosure env closure

    Domain.Pi typ closure -> do
      typ' <- typ
      Syntax.Pi <$> readBack env typ' <*> readBackClosure env closure

    Domain.Fun source domain -> do
      source' <- source
      domain' <- domain
      Syntax.Fun <$> readBack env source' <*> readBack env domain'

readBackClosure :: Domain.Env v -> Domain.Closure -> M (Bound.Scope () Syntax.Term v)
readBackClosure env closure = do
  let
    (env', v) =
      Domain.extend env

  closure' <- evalClosure closure $ pure $ Domain.var v
  Bound.Scope <$> readBack env' closure'

readBackNeutral :: Domain.Env v -> Domain.Head -> Domain.Spine -> M (Syntax.Term v)
readBackNeutral env hd spine =
  case spine of
    Tsil.Nil ->
      pure $ readBackHead env hd

    Tsil.Snoc spine' arg -> do
      arg' <- arg
      Syntax.App <$> readBackNeutral env hd spine' <*> readBack env arg'

readBackHead :: Domain.Env v -> Domain.Head -> Syntax.Term v
readBackHead env hd =
  case hd of
    Domain.Var v ->
      Syntax.Var $ Domain.lookupEnv env v

    Domain.Global g ->
      Syntax.Global g
