{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module Command.Watch where

import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Data.Time.Clock
import qualified Driver
import qualified Error.Hydrated
import qualified FileSystem
import Prettyprinter (Doc)
import qualified Prettyprinter as Doc
import Prettyprinter.Render.Text (putDoc)
import Protolude hiding (check)
import qualified System.Console.ANSI
import qualified System.FSNotify as FSNotify

watch :: [FilePath] -> IO ()
watch argumentFiles = do
  watcher <- FileSystem.watcherFromArguments argumentFiles
  signalChangeVar <- newEmptyMVar
  fileStateVar <- newMVar mempty
  FSNotify.withManager \manager -> do
    stopListening <- FileSystem.runWatcher watcher manager \projectFiles -> do
      modifyMVar_ fileStateVar \projectFiles' ->
        pure
          projectFiles
            { FileSystem.changedFiles =
                projectFiles.changedFiles <> projectFiles'.changedFiles
            }
      void $ tryPutMVar signalChangeVar ()

    (`finally` stopListening) $ do
      driverState <- Driver.initialState
      forever $ do
        projectFiles <- waitForChanges signalChangeVar fileStateVar driverState
        checkAndPrintErrors driverState projectFiles

waitForChanges
  :: MVar ()
  -> MVar FileSystem.ProjectFiles
  -> Driver.State (Doc ann)
  -> IO FileSystem.ProjectFiles
waitForChanges signalChangeVar fileStateVar driverState = do
  projectFiles <-
    modifyMVar fileStateVar \projectFiles ->
      pure (projectFiles {FileSystem.changedFiles = mempty}, projectFiles)

  if HashSet.null projectFiles.changedFiles
    then do
      takeMVar signalChangeVar
      waitForChanges signalChangeVar fileStateVar driverState
    else pure projectFiles

checkAndPrintErrors
  :: Driver.State (Doc ann)
  -> FileSystem.ProjectFiles
  -> IO ()
checkAndPrintErrors driverState projectFiles = do
  startTime <- getCurrentTime
  (_, errs) <-
    Driver.runIncrementalTask
      driverState
      projectFiles.changedFiles
      (HashSet.fromList projectFiles.sourceDirectories)
      (fmap Right projectFiles.fileContents)
      Error.Hydrated.pretty
      Driver.Prune
      Driver.checkAll
  endTime <- getCurrentTime

  System.Console.ANSI.clearScreen
  forM_ errs \err ->
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
