{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Command.Compile where

import qualified Compiler
import Data.String (String)
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

compile :: [FilePath] -> Maybe FilePath -> Maybe FilePath -> Maybe String -> IO ()
compile argumentFiles maybeAssemblyDir maybeOutputFile maybeOptimisationLevel = do
  startTime <- getCurrentTime
  (sourceDirectories, filePaths) <- Project.filesFromArguments argumentFiles
  ((), errs) <-
    withAssemblyDirectory maybeAssemblyDir $ \assemblyDir ->
    withOutputFile maybeOutputFile $ \outputFile ->
      Driver.runTask sourceDirectories filePaths Error.Hydrated.pretty $
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

withOutputFile :: Maybe FilePath -> (FilePath -> IO a) -> IO a
withOutputFile maybeOutputFile k' =
  case maybeOutputFile of
    Nothing ->
      withTempFile "." "temp.exe" $ \outputFile outputFileHandle -> do
        hClose outputFileHandle
        k' outputFile

    Just o -> do
      o' <- makeAbsolute o
      k' o'

withAssemblyDirectory :: Maybe FilePath -> (FilePath -> IO a) -> IO a
withAssemblyDirectory maybeAssemblyDir k =
  case maybeAssemblyDir of
    Nothing ->
      withSystemTempDirectory "sixten" k

    Just dir -> do
      createDirectoryIfMissing True dir
      k dir
