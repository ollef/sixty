{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (force, evaluate)

import qualified Domain
import Environment (Environment)
import qualified Environment
import Index
import Monad
import qualified Syntax
import qualified Tsil

evaluate :: Environment v (Lazy Domain.Value) -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var v ->
      force $ Environment.lookup env v

    Syntax.Meta i ->
      pure $ Domain.meta i

    Syntax.Global g ->
      pure $ Domain.global g -- TODO

    Syntax.Let t (Scope s) -> do
      t' <- lazy $ evaluate env t
      evaluate (Environment.Snoc env t') s

    Syntax.Pi t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Pi t' (Domain.Closure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ evaluate env t1
      t2' <- lazy $ evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam s ->
      pure $ Domain.Lam (Domain.Closure env s)

    Syntax.App t1 t2 -> do
      t1' <- evaluate env t1
      t2' <- lazy $ evaluate env t2
      apply t1' t2'

apply :: Domain.Value -> Lazy Domain.Value -> M Domain.Value
apply fun arg =
  case fun of
    Domain.Lam closure ->
      evaluateClosure closure arg

    Domain.Neutral hd args ->
      pure $ Domain.Neutral hd (Tsil.Snoc args arg)

    _ ->
      panic "applying non-function"

evaluateClosure :: Domain.Closure -> Lazy Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure env (Scope body)) x =
  evaluate (Environment.Snoc env x) body

readBack :: Environment.Size v -> Domain.Value -> M (Syntax.Term v)
readBack size value =
  case value of
    Domain.Neutral hd spine ->
      readBackNeutral size hd spine

    Domain.Lam closure ->
      Syntax.Lam <$> readBackClosure size closure

    Domain.Pi typ closure -> do
      typ' <- force typ
      Syntax.Pi <$> readBack size typ' <*> readBackClosure size closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun <$> readBack size source' <*> readBack size domain'

readBackClosure :: Environment.Size v -> Domain.Closure -> M (Scope Syntax.Term v)
readBackClosure size closure = do
  let
    (size', v) =
      Environment.extendSize size

  closure' <- evaluateClosure closure $ Lazy $ pure $ Domain.var v
  Scope <$> readBack size' closure'

readBackNeutral :: Environment.Size v -> Domain.Head -> Domain.Spine -> M (Syntax.Term v)
readBackNeutral size hd spine =
  case spine of
    Tsil.Nil ->
      pure $ readBackHead size hd

    Tsil.Snoc spine' arg -> do
      arg' <- force arg
      Syntax.App <$> readBackNeutral size hd spine' <*> readBack size arg'

readBackHead :: Environment.Size v -> Domain.Head -> Syntax.Term v
readBackHead size hd =
  case hd of
    Domain.Var v ->
      Syntax.Var $ Index.fromLevel v size

    Domain.Meta m ->
      Syntax.Meta m

    Domain.Global g ->
      Syntax.Global g
