{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (force)

import qualified Data.Dependent.Map as DMap
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.String
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Rock

import Error (Error)
import qualified Meta
import qualified Name
import qualified Presyntax
import qualified Pretty
import Query (Query)
import qualified Query
import qualified Rules

main :: IO ()
main = do
  [inputModule] <- getArgs
  parseAndTypeCheck (fromString inputModule)

runQueryTask :: Task Query a -> IO (a, [Error])
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

  result <- runTask sequentially rules task
  errorsMap <- readMVar errorsVar
  let
    errors =
      flip foldMap (DMap.toList errorsMap) $ \(_ DMap.:=> Const errs) ->
        errs
  return (result, errors)

parseAndTypeCheck :: Name.Module -> IO ()
parseAndTypeCheck module_ = do
  ((), errs) <- runQueryTask $ do
    defs <- fetch $ Query.ParsedModule module_
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . Presyntax.definitionName <$> defs
    forM_ names $ \name -> do
      (type_, _) <- fetch $ Query.ElaboratedType name
      liftIO $ putDoc $ pretty name <> " : " <> Pretty.prettyTerm 0 Pretty.empty type_ <> line
      maybeDef <- fetch $ Query.ElaboratedDefinition name
      liftIO $ forM_ maybeDef $ \(def, _, metas) -> do
        putDoc $ pretty name <> " = " <> Pretty.prettyTerm 0 Pretty.empty def <> line
        forM_ (sortOn fst $ HashMap.toList metas) $ \(Meta.Index index, (metaDef, metaType)) -> do
          putDoc $ "  ?" <> pretty index <> " : " <> Pretty.prettyTerm 0 Pretty.empty metaType <> line
          putDoc $ "  ?" <> pretty index <> " = " <> Pretty.prettyTerm 0 Pretty.empty metaDef <> line
  print errs
