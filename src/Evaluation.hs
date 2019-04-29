{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (force, evaluate)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Domain
import Index
import Monad
import qualified Syntax
import qualified Tsil
import Var

-------------------------------------------------------------------------------
-- Evaluation environments

data Environment v = Environment
  { nextVar :: !(IORef Var)
  , vars :: Seq Var
  , values :: HashMap Var (Lazy Domain.Value)
  }

extend
  :: Environment v
  -> Lazy Domain.Value
  -> IO (Environment (Succ v))
extend env value = do
  var@(Var v) <- readIORef (nextVar env)
  writeIORef (nextVar env) (Var (v + 1))
  pure env
    { vars = vars env Seq.|> var
    , values = HashMap.insert var value (values env)
    }

lookupValue :: Index v -> Environment v -> Lazy Domain.Value
lookupValue (Index i) env =
  values env HashMap.! Seq.index (vars env) (Seq.length (vars env) - i - 1)

-------------------------------------------------------------------------------

evaluate :: Environment v -> Syntax.Term v -> M Domain.Value
evaluate env term =
  case term of
    Syntax.Var v ->
      force $ lookupValue v env

    Syntax.Meta i ->
      pure $ Domain.meta i

    Syntax.Global g ->
      pure $ Domain.global g -- TODO

    Syntax.Let t (Scope s) -> do
      t' <- lazy $ evaluate env t
      env' <- extend env t'
      evaluate env' s

    Syntax.Pi t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Pi t' (makeClosure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ evaluate env t1
      t2' <- lazy $ evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam s ->
      pure $ Domain.Lam (makeClosure env s)

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
evaluateClosure (Domain.Closure f) = f

makeClosure :: Environment v -> Scope Syntax.Term v -> Domain.Closure
makeClosure env (Scope body) =
  Domain.Closure $ \argument -> do
    env' <- extend env argument
    evaluate env' body
