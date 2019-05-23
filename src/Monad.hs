{-# language OverloadedStrings #-}
module Monad where

import Protolude hiding (State)

import Control.Monad.Trans.Except (ExceptT, runExceptT)
import Data.IORef
import Rock

import Error (Error)
import Query (Query)
import qualified Tsil
import Tsil (Tsil)
import Var

type M = ExceptT Error (ReaderT State (Task Query))

data State = State
  { nextVar :: !(MVar Var)
  , errors :: !(MVar (Tsil Error))
  }

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
  ref <- asks nextVar
  liftIO $
    modifyMVar ref $ \var@(Var i) ->
      pure (Var $ i + 1, var)

runM :: M a -> Task Query (Maybe a, [Error])
runM r = do
  nextVarVar <- liftIO $ newMVar $ Var 0
  errorsVar <- liftIO $ newMVar mempty
  eitherResult <- runReaderT (runExceptT r) State
    { nextVar = nextVarVar
    , errors = errorsVar
    }
  errs <- liftIO $ readMVar errorsVar
  case eitherResult of
    Left err ->
      pure (Nothing, toList $ Tsil.Snoc errs err)

    Right result ->
      pure (Just result, toList errs)

report :: Error -> M ()
report err = do
  errorsVar <- asks errors
  liftIO $ modifyMVar_ errorsVar $ \errs ->
    pure $ Tsil.Snoc errs err

try :: M a -> M (Maybe a)
try m =
  (Just <$> m) `catchError` \err -> do
    report err
    pure Nothing

try_ :: M () -> M Bool
try_ m =
  (True <$ m) `catchError` \err -> do
    report err
    pure False
