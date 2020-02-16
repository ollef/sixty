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

newtype Project = Project
  { _sourceDirectories :: [FilePath]
  }

Aeson.deriveJSON (Aeson.aesonDrop 1 Aeson.trainCase) ''Project

filesFromArguments :: [FilePath] -> IO ([FilePath], HashSet FilePath)
filesFromArguments files =
  case files of
    [] -> do
      workingDirectory <- Directory.getCurrentDirectory
      filesFromProjectInDirectory workingDirectory

    _ ->
      fmap mconcat $
        forM files $ \file -> do
          isDir <- Directory.doesDirectoryExist file
          isFile <- Directory.doesFileExist file
          case () of
            _ | isDir ->
                (,) [file] <$> listDirectoryRecursive isSourcePath file

              | isFile, isProjectPath file ->
                listProjectFile file

              | isFile, isSourcePath file ->
                pure ([FilePath.takeDirectory file], HashSet.singleton file)

              | otherwise ->
                -- TODO report error
                pure mempty

filesFromProjectInDirectory :: FilePath -> IO ([FilePath], HashSet FilePath)
filesFromProjectInDirectory directory = do
  maybeProjectFile <- findProjectFile directory
  case maybeProjectFile of
    Nothing ->
      -- TODO report error
      pure mempty

    Just file ->
      listProjectFile file

findProjectFile :: FilePath -> IO (Maybe FilePath)
findProjectFile directory = do
  let
    candidateDirectories =
      map FilePath.joinPath $
      reverse $
      drop 1 $
      inits $
      FilePath.splitDirectories directory
  runMaybeT $ asum $
    foreach candidateDirectories $ \candidateDirectory -> do
      let
        file =
          candidateDirectory FilePath.</> "sixten.json"
      fileExists <- liftIO $ Directory.doesFileExist file
      guard fileExists
      pure file

listProjectFile :: FilePath -> IO ([FilePath], HashSet FilePath)
listProjectFile file = do
  maybeProject <- Aeson.decodeFileStrict file
  case maybeProject of
    Nothing ->
      -- TODO report error
      pure mempty

    Just project ->
      listProject project

listProject :: Project -> IO ([FilePath], HashSet FilePath)
listProject project = do
  sourceDirectories <- mapM Directory.canonicalizePath $ _sourceDirectories project
  fmap ((,) sourceDirectories . mconcat) $
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
