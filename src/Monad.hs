{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Monad where

import Protolude hiding (try, State)

import Data.IORef.Lifted
import Control.Monad.Trans.Control
import Rock
import System.IO.Unsafe (unsafeDupablePerformIO)

import Query (Query)
import Var

type M = ReaderT State (Task Query)

newtype State = State
  { nextVar :: IORef Var
  }

data Lazy a = Lazy a

{-# inline force #-}
force :: Lazy a -> M a
force (Lazy a) =
  liftIO $ evaluate a

{-# noinline lazy #-}
lazy :: M a -> M (Lazy a)
lazy m =
  liftBaseWith $ \runInIO ->
    pure $ Lazy $ unsafeDupablePerformIO $ runInIO m

eager :: a -> Lazy a
eager =
  Lazy

freshVar :: M Var
freshVar = do
  ref <- asks nextVar
  atomicModifyIORef ref $ \var@(Var i) ->
    (Var $ i + 1, var)

runM :: M a -> Task Query a
runM r = do
  nextVarVar <- newIORef $ Var 0
  runReaderT r State
    { nextVar = nextVarVar
    }

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b <- p x
  if b then
    allM p xs
  else
    return False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = return False
anyM p (x:xs) = do
  b <- p x
  if b then
    return True
  else
    anyM p xs
