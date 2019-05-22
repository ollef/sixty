{-# language OverloadedStrings #-}
module Monad where

import Protolude

import Data.IORef
import Rock

import Error (Error)
import Query (Query)
import Var

type M = ReaderT (IORef Var) (Task Query)

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

runM :: M a -> Task Query a
runM r = do
  ref <- liftIO $ newIORef $ Var 0
  runReaderT r ref

report :: Error -> M ()
report = undefined
