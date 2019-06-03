{-# language OverloadedStrings #-}
module Monad where

import Protolude hiding (State)

import Control.Monad.Trans.Except (ExceptT, runExceptT)
import Data.IORef
import Rock

import qualified Error
import Query (Query)
import Var

type M = ExceptT Error.Elaboration (ReaderT State (Task Query))

newtype State = State
  { nextVar :: IORef Var
  }

newtype Lazy a = Lazy { force :: M a }

lazy :: MonadIO m => M a -> m (Lazy a)
lazy m = liftIO $ do
  ref <- newIORef $ panic "Can't happen, I promise!"
  writeIORef ref $ do
    result <- m
    liftIO $ writeIORef ref $ pure result
    pure result
  pure $ Lazy $ join $ liftIO $ readIORef ref

freshVar :: M Var
freshVar = do
  ref <- asks nextVar
  liftIO $
    atomicModifyIORef ref $ \var@(Var i) ->
      (Var $ i + 1, var)

runM :: M a -> Task Query (Either Error.Elaboration a)
runM r = do
  nextVarVar <- liftIO $ newIORef $ Var 0
  runReaderT (runExceptT r) State
    { nextVar = nextVarVar
    }
