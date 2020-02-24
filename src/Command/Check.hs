{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Command.Check where

import Protolude hiding (withAsync, wait)

import Control.Concurrent.Async.Lifted.Safe
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

check :: [FilePath] -> Bool -> IO ()
check argumentFiles printElaborated = do
  (sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  ((), errs) <- Driver.runTask sourceDirectories filePaths Error.Hydrated.pretty $ do
    if printElaborated then
      withAsync (void Driver.checkAll) $ \checkedAll -> do
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
        wait checkedAll
    else
      void Driver.checkAll
  forM_ errs $ \err ->
    putDoc $ err <> line
