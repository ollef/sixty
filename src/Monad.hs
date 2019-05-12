{-# language OverloadedStrings #-}
module Monad where

import Protolude

import Data.IORef

import Var

type M = ReaderT (IORef Var) IO

newtype Lazy a = Lazy { force :: M a }

lazy :: M a -> M (Lazy a)
lazy m = liftIO $ do
  ref <- newIORef $ panic "Can't happen, I promise!"
  writeIORef ref $ do
    result <- m
    liftIO $ writeIORef ref $ pure result
    pure result
  pure $ Lazy $ join $ liftIO $ readIORef ref

freshVar :: M Var
freshVar = do
  ref <- ask
  liftIO $ do
    var@(Var i) <- readIORef ref
    writeIORef ref $ Var $ i + 1
    pure var

runM :: M a -> IO a
runM r = do
  ref <- newIORef $ Var 0
  runReaderT r ref
