{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ScopedTypeVariables #-}
module FileSystem where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Aeson as Aeson
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified System.Directory as Directory
import qualified System.FilePath as FilePath
import qualified System.FSNotify as FSNotify

import qualified Project

newtype Watcher key value = Watcher
  { runWatcher
    :: FSNotify.WatchManager
    -> (key -> value -> IO ())
    -> IO FSNotify.StopListening
  } deriving (Functor)

instance Bifunctor Watcher where
  bimap f g (Watcher watcher) =
    Watcher $ \manager onChange ->
      watcher manager (\key value -> onChange (f key) (g value))

instance Monoid value => Semigroup (Watcher key value) where
  Watcher watcher1 <> Watcher watcher2 =
    Watcher $ \manager onChange -> do
      valuesVar <- newMVar mempty
      stopListening1 <- watcher1 manager $ \key value1 -> do
        value <- modifyMVar valuesVar $ \(_, value2) ->
          pure ((value1, value2), value1 <> value2)
        onChange key value
      stopListening2 <- watcher2 manager $ \key value2 -> do
        value <- modifyMVar valuesVar $ \(value1, _) ->
          pure ((value1, value2), value1 <> value2)
        onChange key value
      pure $ stopListening1 <> stopListening2

instance Monoid value => Monoid (Watcher key value) where
  mempty =
    Watcher mempty

instance Monoid key => Applicative (Watcher key) where
  pure x =
    Watcher $ \_ onChange -> do
      onChange mempty x
      pure mempty

  (<*>) =
    ap

instance Monoid key => Monad (Watcher key) where
  Watcher watcher1 >>= f =
    Watcher $ \manager onChange -> do
      stopListening2Var <- newMVar mempty
      stopListening1 <- watcher1 manager $ \key value1 ->
        modifyMVar_ stopListening2Var $ \stopListening2 -> do
          stopListening2
          runWatcher (f value1) manager $ \key' -> onChange (key <> key')
      pure $ do
        stopListening1
        modifyMVar_ stopListening2Var $ \stopListening2 -> do
          stopListening2
          mempty

bindForM
  :: (Eq key, Hashable key, Monoid value)
  => Watcher () (HashSet key)
  -> (key -> Watcher key' value)
  -> Watcher key' value
bindForM (Watcher watchKeys) watchKey =
  Watcher $ \manager onChange -> do
    valuesVar <- newMVar mempty
    stopListeningVar <- newMVar mempty
    let
      onOuterChange () keys' = do
        stopKeys <- modifyMVar stopListeningVar $ \stopListenings -> do
          let
            keys'Map =
              HashSet.toMap keys'

            stopKeys =
              HashMap.difference stopListenings keys'Map

            keepKeys =
              HashMap.intersection stopListenings keys'Map

            startKeys =
              HashMap.difference keys'Map stopListenings

          sequence_ stopKeys

          startKeys' <- flip HashMap.traverseWithKey startKeys $ \key () ->
            runWatcher (watchKey key) manager $ onInnerChange key

          pure (keepKeys <> startKeys', stopKeys)

        modifyMVar_ valuesVar $ \values ->
          pure $ HashMap.difference values stopKeys

      onInnerChange key key' value = do
        keys' <- modifyMVar valuesVar $ \values -> do
          let
            keys' =
              HashMap.insert key value values
          pure (keys', keys')
        onChange key' $ fold keys'

    watchKeys manager onOuterChange

-------------------------------------------------------------------------------

watcherFromArguments :: [FilePath] -> IO (Watcher (HashSet FilePath) (HashMap FilePath Text))
watcherFromArguments files =
  case files of
    [] -> do
      workingDirectory <- Directory.getCurrentDirectory
      maybeProjectFile <- Project.findProjectFile workingDirectory
      case maybeProjectFile of
        Nothing ->
          mempty

        Just projectFile -> do
          projectFile' <- Directory.canonicalizePath projectFile
          pure $ projectWatcher projectFile'

    _ ->
      fmap mconcat $
        forM files $ \file -> do
          file' <- Directory.canonicalizePath file
          isDir <- Directory.doesDirectoryExist file'
          case () of
            _ | isDir ->
                pure $ directoryWatcher Project.isSourcePath file'

              | Project.isProjectPath file' ->
                pure $ projectWatcher file'

              | Project.isSourcePath file' ->
                pure $
                  bimap
                    (const $ HashSet.singleton file')
                    (foldMap $ HashMap.singleton file') $
                  fileWatcher file'

              | otherwise ->
                -- TODO report error?
                mempty

projectWatcher :: FilePath -> Watcher (HashSet FilePath) (HashMap FilePath Text)
projectWatcher file =
  bindForM (foldMap (HashSet.fromList . Project._domainDirectories) <$> jsonFileWatcher file) $
    directoryWatcher Project.isSourcePath

fileWatcher :: FilePath -> Watcher () (Maybe Text)
fileWatcher filePath = Watcher $ \manager onChange -> do
  maybeOriginalText <- readFileText filePath
  onChange () maybeOriginalText
  FSNotify.watchDir
    manager
    (FilePath.takeDirectory filePath)
    ((== filePath) . FSNotify.eventPath)
    (\_ -> do
      maybeText <- readFileText filePath
      onChange () maybeText
    )

jsonFileWatcher :: Aeson.FromJSON a => FilePath -> Watcher () (Maybe a)
jsonFileWatcher filePath = Watcher $ \manager onChange -> do
  maybeOriginalValue <- readFileJSON filePath
  onChange () maybeOriginalValue
  FSNotify.watchDir
    manager
    (FilePath.takeDirectory filePath)
    ((== filePath) . FSNotify.eventPath)
    (\_ -> do
      maybeValue <- readFileJSON filePath
      onChange () maybeValue
    )

directoryWatcher
  :: (FilePath -> Bool)
  -> FilePath
  -> Watcher (HashSet FilePath) (HashMap FilePath Text)
directoryWatcher predicate directory = Watcher $ \manager onChange -> do
  filesVar <- newEmptyMVar
  stopListening <-
    FSNotify.watchTree manager directory (predicate . FSNotify.eventPath) $ \event -> do
      let
        filePath =
          FSNotify.eventPath event
      maybeText <- readFileText filePath
      files <- modifyMVar filesVar $ \files -> do
        let
          files' =
            HashMap.alter (const maybeText) filePath files
        pure (files', files')
      onChange (HashSet.singleton filePath) files
  files <- listDirectoryRecursive predicate directory
  putMVar filesVar files
  onChange (HashSet.fromMap $ void files) files
  pure stopListening

listDirectoryRecursive :: (FilePath -> Bool) -> FilePath -> IO (HashMap FilePath Text)
listDirectoryRecursive predicate directory = do
  files <- Directory.listDirectory directory
  fmap mconcat $ forM files $ \file -> do
    path <- Directory.canonicalizePath $ directory FilePath.</> file
    isDir <- Directory.doesDirectoryExist path
    if isDir then
      listDirectoryRecursive predicate path

    else if predicate path then do
      text <- readFile path
      pure $ HashMap.singleton path text

    else
      mempty

readFileText :: FilePath -> IO (Maybe Text)
readFileText file =
  do
    Just <$> readFile file
  `catch` \(_ :: IOException) ->
    pure Nothing

readFileJSON :: Aeson.FromJSON a => FilePath -> IO (Maybe a)
readFileJSON file =
  do
    Aeson.decodeFileStrict file
  `catch` \(_ :: IOException) ->
    pure Nothing
