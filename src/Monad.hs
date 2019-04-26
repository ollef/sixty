{-# language OverloadedStrings #-}
module Monad where

import Protolude

import Data.IORef

type M = IO

lazy :: M a -> M (M a)
lazy m = do
  ref <- newIORef $ panic "lazy IORef!"
  writeIORef ref $ do
    result <- m
    writeIORef ref $ pure result
    pure result
  pure $ join $ readIORef ref
