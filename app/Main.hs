{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Protolude hiding (force)

import qualified Data.HashSet as HashSet
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text
import Rock

import qualified Driver
import qualified Error
import qualified Name
import qualified Pretty
import qualified Query
import qualified Syntax

main :: IO ()
main = do
  filePaths <- getArgs
  parseAndTypeCheck filePaths

parseAndTypeCheck :: [FilePath] -> IO ()
parseAndTypeCheck filePaths = do
  ((), errs) <- Driver.runTask filePaths $
    forM_ filePaths $ \filePath -> do
      (module_, _, defs) <- fetch $ Query.ParsedFile filePath
      let
        names =
          HashSet.fromList $
            Name.Qualified module_ . fst . snd <$> defs
      emptyPrettyEnv <- Pretty.emptyM module_
      liftIO $ putDoc $ "module" <+> pretty module_ <> line <> line
      forM_ names $ \name -> do
        type_ <- fetch $ Query.ElaboratedType name
        liftIO $ putDoc $ Pretty.prettyDefinition emptyPrettyEnv name (Syntax.TypeDeclaration type_) <> line
        maybeDef <- fetch $ Query.ElaboratedDefinition name
        liftIO $ do
          forM_ maybeDef $ \(def, _) ->
            putDoc $ Pretty.prettyDefinition emptyPrettyEnv name def <> line
          putDoc line
  forM_ errs $ \(filePath, lineColumn, lineText, err) ->
    liftIO $ putDoc $ Error.pretty filePath lineColumn lineText err <> line
