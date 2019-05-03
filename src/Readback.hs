{-# language DeriveAnyClass #-}
module Readback where

import Protolude hiding (Seq, force, evaluate)

import Data.IORef

import qualified Domain
import qualified Evaluation
import Index
import Monad
import Sequence (Seq)
import qualified Sequence as Seq
import qualified Syntax
import qualified Tsil
import Var

-------------------------------------------------------------------------------
-- Readback environments

data Environment v = Environment
  { nextVar :: !(IORef Var)
  , vars :: Seq Var
  }

empty :: IORef Var -> Environment Void
empty nextVar_ = Environment
  { nextVar = nextVar_
  , vars = mempty
  }

extend
  :: Environment v
  -> IO (Environment (Succ v), Var)
extend env = do
  var@(Var v) <- readIORef (nextVar env)
  writeIORef (nextVar env) (Var (v + 1))
  pure
    ( env
      { vars = vars env Seq.:> var
      }
    , var
    )

lookupIndex :: Var -> Environment v -> Maybe (Index v)
lookupIndex var context =
  case Seq.elemIndex var (vars context) of
    Nothing ->
      Nothing

    Just i ->
      Just (Index (Seq.length (vars context) - i - 1))

-------------------------------------------------------------------------------

data ScopingException = ScopingException
  deriving (Eq, Show, Exception)

-------------------------------------------------------------------------------

readback :: Environment v -> Domain.Value -> M (Syntax.Term v)
readback env value =
  case value of
    Domain.Neutral hd spine ->
      readbackNeutral env hd spine

    Domain.Lam name type_ closure -> do
      type' <- force type_
      Syntax.Lam name <$> readback env type' <*> readbackClosure env closure

    Domain.Pi name type_ closure -> do
      type' <- force type_
      Syntax.Pi name <$> readback env type' <*> readbackClosure env closure

    Domain.Fun source domain -> do
      source' <- force source
      domain' <- force domain
      Syntax.Fun <$> readback env source' <*> readback env domain'

readbackClosure :: Environment v -> Domain.Closure -> M (Scope Syntax.Term v)
readbackClosure env closure = do
  (env', v) <- extend env

  closure' <- Evaluation.evaluateClosure closure $ Lazy $ pure $ Domain.var v
  readback env' closure'

readbackNeutral :: Environment v -> Domain.Head -> Domain.Spine -> M (Syntax.Term v)
readbackNeutral env hd spine =
  case spine of
    Tsil.Nil ->
      readbackHead env hd

    Tsil.Snoc spine' arg -> do
      arg' <- force arg
      Syntax.App <$> readbackNeutral env hd spine' <*> readback env arg'

readbackHead :: Environment v -> Domain.Head -> M (Syntax.Term v)
readbackHead env hd =
  case hd of
    Domain.Var v ->
      case lookupIndex v env of
        Just i ->
          pure $ Syntax.Var i

        Nothing ->
          throwIO ScopingException

    Domain.Meta m ->
      pure $ Syntax.Meta m

    Domain.Global g ->
      pure $ Syntax.Global g
