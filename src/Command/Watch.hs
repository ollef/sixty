{-# LANGUAGE OverloadedStrings #-}

module Command.Watch where

import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Prettyprinter (Doc)
import qualified Prettyprinter as Doc
import Prettyprinter.Render.Text (putDoc)
import Data.Time.Clock
import qualified Driver
import qualified Error.Hydrated
import qualified FileSystem
import Protolude hiding (check)
import qualified System.Console.ANSI
import qualified System.FSNotify as FSNotify

watch :: [FilePath] -> IO ()
watch argumentFiles = do
  watcher <- FileSystem.watcherFromArguments argumentFiles
  signalChangeVar <- newEmptyMVar
  fileStateVar <- newMVar mempty
  FSNotify.withManagerConf config $ \manager -> do
    stopListening <- FileSystem.runWatcher watcher manager $ \(changedFiles, sourceDirectories, files) -> do
      modifyMVar_ fileStateVar $ \(changedFiles', _, _) ->
        pure (changedFiles <> changedFiles', sourceDirectories, files)
      void $ tryPutMVar signalChangeVar ()

    (`finally` stopListening) $ do
      driverState <- Driver.initialState
      forever $ do
        (changedFiles, sourceDirectories, files) <- waitForChanges signalChangeVar fileStateVar driverState
        checkAndPrintErrors driverState changedFiles sourceDirectories files
  where
    config =
      FSNotify.defaultConfig
        { FSNotify.confDebounce = FSNotify.Debounce 0.010
        }

waitForChanges ::
  MVar () ->
  MVar (HashSet FilePath, [FileSystem.Directory], HashMap FilePath Text) ->
  Driver.State (Doc ann) ->
  IO (HashSet FilePath, [FileSystem.Directory], HashMap FilePath Text)
waitForChanges signalChangeVar fileStateVar driverState = do
  (changedFiles, sourceDirectories, files) <-
    modifyMVar fileStateVar $ \(changedFiles, sourceDirectories, files) ->
      pure ((mempty, sourceDirectories, files), (changedFiles, sourceDirectories, files))

  if HashSet.null changedFiles
    then do
      takeMVar signalChangeVar
      waitForChanges signalChangeVar fileStateVar driverState
    else pure (changedFiles, sourceDirectories, files)

checkAndPrintErrors ::
  Driver.State (Doc ann) ->
  HashSet FilePath ->
  [FileSystem.Directory] ->
  HashMap FilePath Text ->
  IO ()
checkAndPrintErrors driverState changedFiles sourceDirectories files = do
  startTime <- getCurrentTime
  (_, errs) <-
    Driver.runIncrementalTask
      driverState
      changedFiles
      sourceDirectories
      files
      Error.Hydrated.pretty
      Driver.Prune
      Driver.checkAll
  endTime <- getCurrentTime

  System.Console.ANSI.clearScreen
  forM_ errs $ \err ->
    putDoc $ err <> Doc.line
  let errorCount =
        length errs
  putText $
    Text.unwords
      [ "Found"
      , show errorCount
      , case errorCount of
          1 -> "error"
          _ -> "errors"
      , "in"
      , show (diffUTCTime endTime startTime) <> "."
      ]
