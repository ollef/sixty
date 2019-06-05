{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (force)

import qualified Data.Dependent.Map as DMap
import qualified Data.HashSet as HashSet
import Data.String
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Rock

import Error (Error)
import qualified Error
import qualified Name
import qualified Presyntax
import qualified Pretty
import Query (Query)
import qualified Query
import qualified Rules
import qualified Span

main :: IO ()
main = do
  [inputModule] <- getArgs
  parseAndTypeCheck (fromString inputModule)

runQueryTask :: Task Query a -> IO (a, [(FilePath, Span.LineColumn, Error)])
runQueryTask task = do
  startedVar <- newMVar mempty
  errorsVar <- newMVar mempty
  let
    writeErrors :: Query a -> [Error] -> Task Query ()
    writeErrors q errs =
      unless (null errs) $
        liftIO $ modifyMVar_ errorsVar $ pure . DMap.insert q (Const errs)

    rules :: Rules Query
    rules =
      memoise startedVar $ writer writeErrors Rules.rules

  runTask sequentially rules $ do
    result <- task
    errorsMap <- liftIO $ readMVar errorsVar
    let
      errors =
        flip foldMap (DMap.toList errorsMap) $ \(_ DMap.:=> Const errs) ->
          errs
    spannedErrors <- forM errors $ \err -> do
      (filePath, span) <- fetch $ Query.ErrorSpan err
      text <- fetch $ Query.ReadFile filePath
      pure (filePath, Span.lineColumn span text, err)
    pure (result, spannedErrors)

parseAndTypeCheck :: Name.Module -> IO ()
parseAndTypeCheck module_ = do
  ((), errs) <- runQueryTask $ do
    defs <- fetch $ Query.ParsedModule module_
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . Presyntax.definitionName . snd <$> defs
    forM_ names $ \name -> do
      type_ <- fetch $ Query.ElaboratedType name
      liftIO $ putDoc $ pretty name <> " : " <> Pretty.prettyTerm 0 Pretty.empty type_ <> line
      maybeDef <- fetch $ Query.ElaboratedDefinition name
      liftIO $ forM_ maybeDef $ \(def, _) -> do
        putDoc $ pretty name <> " = " <> Pretty.prettyTerm 0 Pretty.empty def <> line
  forM_ errs $ \(filePath, lineColumn, err) ->
    liftIO $ putDoc $ Error.pretty filePath lineColumn err <> line
