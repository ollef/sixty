{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Command.Compile where

import qualified Compiler
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Time.Clock
import qualified Driver
import qualified Error.Hydrated
import qualified Project
import Protolude hiding (withAsync, wait, moduleName)
import System.Directory
import System.IO
import System.IO.Temp

data Options = Options
  { argumentFiles :: [FilePath]
  , maybeAssemblyDir :: Maybe FilePath
  , maybeOutputFile :: Maybe FilePath
  , maybeOptimisationLevel :: Maybe FilePath
  }

compile :: Options -> IO ()
compile =
  withCompiledExecutable $ const $ pure ()

withCompiledExecutable :: (FilePath -> IO ()) -> Options ->  IO ()
withCompiledExecutable k Options {..} = do
  startTime <- getCurrentTime
  (sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  withAssemblyDirectory maybeAssemblyDir $ \assemblyDir ->
    withOutputFile maybeOutputFile $ \outputFile -> do
      ((), errs) <- Driver.runTask sourceDirectories filePaths Error.Hydrated.pretty $
        Compiler.compile assemblyDir (isJust maybeAssemblyDir) outputFile maybeOptimisationLevel
      endTime <- getCurrentTime
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
      k outputFile

withOutputFile :: Maybe FilePath -> (FilePath -> IO a) -> IO a
withOutputFile maybeOutputFile_ k' =
  case maybeOutputFile_ of
    Nothing ->
      withTempFile "." "temp.exe" $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k' outputFile

    Just o -> do
      o' <- makeAbsolute o
      k' o'

withAssemblyDirectory :: Maybe FilePath -> (FilePath -> IO a) -> IO a
withAssemblyDirectory maybeAssemblyDir_ k =
  case maybeAssemblyDir_ of
    Nothing ->
      withSystemTempDirectory "sixten" k

    Just dir -> do
      createDirectoryIfMissing True dir
      k dir
