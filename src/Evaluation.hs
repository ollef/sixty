{-# language OverloadedStrings #-}
module Evaluation where

import Protolude hiding (Seq, force, evaluate)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import Sequence (Seq)
import qualified Sequence as Seq

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

empty :: IORef Var -> Environment Void
empty nextVar_ =
  Environment
    { nextVar = nextVar_
    , vars = mempty
    , values = mempty
    }

extend
  :: Environment v
  -> Lazy Domain.Value
  -> IO (Environment (Succ v))
extend env value = do
  var@(Var v) <- readIORef (nextVar env)
  writeIORef (nextVar env) (Var (v + 1))
  pure env
    { vars = vars env Seq.:> var
    , values = HashMap.insert var value (values env)
    }

lookupValue :: Index v -> Environment v -> Lazy Domain.Value
lookupValue (Index i) env =
  let
    var = Seq.index (vars env) (Seq.length (vars env) - i - 1)
  in
  fromMaybe
    (Lazy $ pure $ Domain.var var)
    (HashMap.lookup var $ values env)

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

    Syntax.Let _ t _ s -> do
      t' <- lazy $ evaluate env t
      env' <- extend env t'
      evaluate env' s

    Syntax.Pi n t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Pi n t' (makeClosure env s)

    Syntax.Fun t1 t2 -> do
      t1' <- lazy $ evaluate env t1
      t2' <- lazy $ evaluate env t2
      pure $ Domain.Fun t1' t2'

    Syntax.Lam n t s -> do
      t' <- lazy $ evaluate env t
      pure $ Domain.Lam n t' (makeClosure env s)

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
      pure $ Domain.Neutral hd (Tsil.Snoc args arg)

    _ ->
      panic "applying non-function"

applySpine :: Domain.Value -> Domain.Spine -> M Domain.Value
applySpine = foldM apply

evaluateClosure :: Domain.Closure -> Lazy Domain.Value -> M Domain.Value
evaluateClosure (Domain.Closure f) = f

makeClosure :: Environment v -> Scope Syntax.Term v -> Domain.Closure
makeClosure env body =
  Domain.Closure $ \argument -> do
    env' <- extend env argument
    evaluate env' body
