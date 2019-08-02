{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Driver where

import Protolude hiding (force)

import qualified Data.Dependent.Map as DMap
import Rock

import Error (Error)
import Query (Query)
import qualified Query
import qualified Rules
import qualified Span

runTask :: [FilePath] -> Task Query a -> IO (a, [(FilePath, Span.LineColumn, Text, Error)])
runTask files task = do
  startedVar <- newMVar mempty
  errorsVar <- newMVar mempty
  let
    writeErrors :: Query a -> [Error] -> Task Query ()
    writeErrors q errs =
      unless (null errs) $
        liftIO $ modifyMVar_ errorsVar $ pure . DMap.insert q (Const errs)

    rules :: Rules Query
    rules =
      -- traceFetch (\q -> liftIO $ putText $ "fetching " <> show q) (\q _ -> liftIO $ putText $ "fetched " <> show q) $
      memoise startedVar $
      writer writeErrors $
      Rules.rules files

  Rock.runTask sequentially rules $ do
    result <- task
    errorsMap <- liftIO $ readMVar errorsVar
    let
      errors =
        flip foldMap (DMap.toList errorsMap) $ \(_ DMap.:=> Const errs) ->
          errs
    spannedErrors <- forM errors $ \err -> do
      (filePath, span) <- fetch $ Query.ErrorSpan err
      text <- fetch $ Query.FileText filePath
      let
        trimmedSpan =
          Span.trim text span
        (lineColumn, lineText) =
          Span.lineColumn trimmedSpan text
      pure (filePath, lineColumn, lineText, err)
    pure (result, spannedErrors)
