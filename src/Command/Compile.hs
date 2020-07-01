{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import Protolude hiding (withAsync, wait, moduleName)

import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import qualified Data.Text.Lazy.IO as Lazy
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)
import Data.Time.Clock
import LLVM.Pretty (ppllvm)
import Rock
import System.FilePath

import qualified Driver
import qualified Error.Hydrated
import qualified Name
import qualified Project
import qualified Query

compile :: [FilePath] -> IO ()
compile argumentFiles = do
  startTime <- getCurrentTime
  (sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  ((), errs) <- Driver.runTask sourceDirectories filePaths Error.Hydrated.pretty $ do
    forM_ filePaths $ \filePath -> do
      (moduleName, _, defs) <- fetch $ Query.ParsedFile filePath
      let
        names =
          HashSet.fromList $
            Name.Qualified moduleName . fst . snd <$> defs
      liftIO $ putDoc $ "module" <+> pretty moduleName <> line <> line
      forM_ (toList names) $ \name -> do
        cc <- fetch $ Query.ClosureConverted $ Name.Lifted name 0
        liftIO $ print cc
        assembly <- fetch $ Query.Assembly $ Name.Lifted name 0
        cpsAssembly <- fetch $ Query.CPSAssembly $ Name.Lifted name 0
        liftIO $ putDoc $ pretty assembly <> line
        putText ""
        liftIO $ putDoc $ pretty cpsAssembly <> line
        putText ""
      llvmModule <- fetch $ Query.LLVMModule moduleName
      let
        outputFileName =
          replaceBaseName (replaceExtension filePath "ll") ("out" </> takeBaseName filePath)
        prettyPrintedLLVMModule =
          ppllvm llvmModule

      putStrLn prettyPrintedLLVMModule
      liftIO $ Lazy.writeFile outputFileName prettyPrintedLLVMModule
  endTime <- getCurrentTime
  forM_ errs $ \err ->
    putDoc $ err <> line
  let
    errorCount =
      length errs
  putText $ Text.unwords
    [ "Found"
    , show errorCount
    , case errorCount of
      1 -> "error"
      _ -> "errors"
    , "in"
    , show (diffUTCTime endTime startTime) <> "."
    ]
  unless (null errs)
    exitFailure
