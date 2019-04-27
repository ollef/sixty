{-# language OverloadedStrings #-}
module Monad where

import Protolude

import Data.IORef

type M = IO

newtype Lazy a = Lazy { force :: M a }

lazy :: M a -> M (Lazy a)
lazy m = do
  ref <- newIORef $ panic "Can't happen, promise!"
  writeIORef ref $ do
    result <- m
    writeIORef ref $ pure result
    pure result
  pure $ Lazy $ join $ readIORef ref
