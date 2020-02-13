{-# language OverloadedStrings #-}
module Command.Watch where

import Protolude hiding (check)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (Doc)
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.Text.Prettyprint.Doc.Render.Text (putDoc)
import Data.Time.Clock
import qualified System.Console.ANSI
import qualified System.FSNotify as FSNotify

import qualified Driver
import qualified Error.Hydrated
import qualified FileSystem

watch :: [FilePath] -> IO ()
watch argumentFiles = do
  watcher <- FileSystem.watcherFromArguments argumentFiles
  signalChangeVar <- newEmptyMVar
  fileStateVar <- newMVar mempty
  FSNotify.withManagerConf config $ \manager -> do
    stopListening <- FileSystem.runWatcher watcher manager $ \changedFiles files -> do
      modifyMVar_ fileStateVar $ \(changedFiles', _) ->
        pure (changedFiles <> changedFiles', files)
      void $ tryPutMVar signalChangeVar ()

    (`finally` stopListening) $ do
      driverState <- Driver.initialState
      forever $ do
        (changedFiles, files) <- waitForChanges signalChangeVar fileStateVar driverState
        checkAndPrintErrors driverState changedFiles files
  where
    config =
      FSNotify.defaultConfig
        { FSNotify.confDebounce = FSNotify.Debounce 0.010
        }

waitForChanges
  :: MVar ()
  -> MVar (HashSet FilePath, HashMap FilePath Text)
  -> Driver.State (Doc ann)
  -> IO (HashSet FilePath, HashMap FilePath Text)
waitForChanges signalChangeVar fileStateVar driverState = do
  (changedFiles, files) <-
    modifyMVar fileStateVar $ \(changedFiles, files) ->
      pure ((mempty, files), (changedFiles, files))

  if HashSet.null changedFiles then do
    takeMVar signalChangeVar
    waitForChanges signalChangeVar fileStateVar driverState

  else
    pure (changedFiles, files)

checkAndPrintErrors :: Driver.State (Doc ann) -> HashSet FilePath -> HashMap FilePath Text -> IO ()
checkAndPrintErrors driverState changedFiles files = do
  startTime <- getCurrentTime
  (_, errs) <- Driver.runIncrementalTask driverState changedFiles files Error.Hydrated.pretty Driver.Prune $
    Driver.checkAll $ HashMap.keys files
  endTime <- getCurrentTime

  System.Console.ANSI.clearScreen
  forM_ errs $ \err ->
    putDoc $ err <> Doc.line
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
