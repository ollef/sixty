{-# language TemplateHaskell #-}
module Project where

import Protolude 

import Control.Monad.Trans.Maybe
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Casing as Aeson
import qualified Data.Aeson.TH as Aeson
import qualified Data.HashSet as HashSet
import Data.HashSet (HashSet)
import qualified System.Directory as Directory
import qualified System.FilePath as FilePath

data Project = Project
  { _sourceDirectories :: [FilePath]
  }

Aeson.deriveJSON (Aeson.aesonDrop 1 Aeson.trainCase) ''Project

filesFromProjectInWorkingDirectory :: IO (HashSet FilePath)
filesFromProjectInWorkingDirectory = do
  maybeProjectFile <- findProjectFile
  case maybeProjectFile of
    Nothing ->
      -- TODO report error
      pure mempty

    Just file ->
      listProjectFile file

filesFromArguments :: [FilePath] -> IO (HashSet FilePath)
filesFromArguments files =
  case files of
    [] ->
      filesFromProjectInWorkingDirectory

    _ ->
      fmap mconcat $
        forM files $ \file -> do
          isDir <- Directory.doesDirectoryExist file
          isFile <- Directory.doesFileExist file
          case () of
            _ | isDir ->
                listDirectoryRecursive isSourcePath file

              | isFile, isProjectPath file ->
                listProjectFile file

              | isFile, isSourcePath file ->
                pure $ HashSet.singleton file

              | otherwise ->
                -- TODO report error
                pure mempty

findProjectFile :: IO (Maybe FilePath)
findProjectFile = do
  currentDir <- Directory.getCurrentDirectory
  let
    candidateDirectories =
      map FilePath.joinPath $
      reverse $
      drop 1 $
      inits $
      FilePath.splitDirectories currentDir
  runMaybeT $ asum $
    foreach candidateDirectories $ \dir -> do
      let
        file =
          dir FilePath.</> "sixten.json"
      fileExists <- liftIO $ Directory.doesFileExist file
      guard fileExists
      pure file

listProjectFile :: FilePath -> IO (HashSet FilePath)
listProjectFile file = do
  maybeProject <- Aeson.decodeFileStrict file
  case maybeProject of
    Nothing ->
      -- TODO report error
      pure mempty

    Just project ->
      listProject project

listProject :: Project -> IO (HashSet FilePath)
listProject project =
  fmap mconcat $
    forM (_sourceDirectories project) $
      listDirectoryRecursive isSourcePath

listDirectoryRecursive :: (FilePath -> Bool) -> FilePath -> IO (HashSet FilePath)
listDirectoryRecursive p dir = do
  files <- Directory.listDirectory dir
  fmap mconcat $ forM files $ \file -> do
    let path = dir FilePath.</> file
    isDir <- Directory.doesDirectoryExist path
    if isDir then
      listDirectoryRecursive p path

    else
      pure $ HashSet.fromList [path | p path]

isSourcePath :: FilePath -> Bool
isSourcePath =
  (== ".vix") . FilePath.takeExtension

isProjectPath :: FilePath -> Bool
isProjectPath =
  (== ".json") . FilePath.takeExtension
