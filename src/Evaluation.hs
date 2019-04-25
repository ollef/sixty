{-# language OverloadedStrings #-}
module Evaluation where

import Protolude

import qualified Bound.Scope.Simple as Bound

import qualified Domain
import qualified Syntax
import qualified Tsil

eval :: Syntax.Env Domain.Value v -> Syntax.Term v -> Domain.Value
eval env term =
  case term of
    Syntax.Var v ->
      Syntax.lookupValue env v

    Syntax.Global g ->
      Domain.global g

    Syntax.Let t (Bound.Scope s) ->
      eval (Syntax.Snoc env (eval env t)) s

    Syntax.Pi t s ->
      Domain.Pi (eval env t) (Domain.Closure env s)

    Syntax.Lam s ->
      Domain.Lam (Domain.Closure env s)

    Syntax.App t1 t2 ->
      apply (eval env t1) (eval env t2)

apply :: Domain.Value -> Domain.Value -> Domain.Value
apply fun arg =
  case fun of
    Domain.Lam closure ->
      evalClosure closure arg

    Domain.Neutral hd args ->
      Domain.Neutral hd (Tsil.Snoc args arg)

    _ ->
      panic "applying non-function"

evalClosure :: Domain.Closure -> Domain.Value -> Domain.Value
evalClosure (Domain.Closure env (Bound.Scope body)) x =
  eval (Syntax.Snoc env x) body

readBack :: Domain.Env v -> Domain.Value -> Syntax.Term v
readBack env value =
  case value of
    Domain.Neutral hd spine ->
      readBackNeutral env hd spine

    Domain.Lam closure ->
      Syntax.Lam (readBackClosure env closure)

    Domain.Pi typ closure ->
      Syntax.Pi (readBack env typ) (readBackClosure env closure)

readBackClosure :: Domain.Env v -> Domain.Closure -> Bound.Scope () Syntax.Term v
readBackClosure env closure = do
  let
    (env', v) =
      Domain.extend env
  Bound.Scope
    $ readBack env'
    $ evalClosure closure $ Domain.var v

readBackNeutral :: Domain.Env v -> Domain.Head -> Domain.Spine -> Syntax.Term v
readBackNeutral env hd spine =
  case spine of
    Tsil.Nil ->
      readBackHead env hd

    Tsil.Snoc spine' arg ->
      Syntax.App (readBackNeutral env hd spine') (readBack env arg)

readBackHead :: Domain.Env v -> Domain.Head -> Syntax.Term v
readBackHead env hd =
  case hd of
    Domain.Var v ->
      Syntax.Var $ Domain.lookupEnv env v

    Domain.Global g ->
      Syntax.Global g
