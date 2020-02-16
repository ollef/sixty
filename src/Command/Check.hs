{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Command.Check where

import Protolude

import qualified Data.HashSet as HashSet
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)
import Rock

import qualified Driver
import qualified Error.Hydrated
import qualified Name
import qualified Pretty
import qualified Project
import qualified Query
import qualified Syntax

check :: [FilePath] -> IO ()
check argumentFiles = do
  (_sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  ((), errs) <- Driver.runTask (HashSet.toList filePaths) Error.Hydrated.pretty $
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
  forM_ errs $ \err ->
    putDoc $ err <> line
