{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Main where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Rock
import System.Directory
import System.FilePath
import qualified Test.Tasty as Tasty
import qualified Test.Tasty.HUnit as Tasty

import qualified Driver
import Error (Error)
import qualified Error
import qualified Error.Hydrated
import qualified Error.Hydrated as Error (Hydrated)
import qualified FileSystem
import qualified Name
import qualified Query

main :: IO ()
main = do
  singlesDirectory <- canonicalizePath "tests/singles"
  multisDirectory <- canonicalizePath "tests/multis"

  let
    isSourceFile =
      (== ".vix") . takeExtension

  singleFiles <- listDirectoryRecursive isSourceFile singlesDirectory
  multiFiles <- listDirectoriesWithFilesMatching isSourceFile multisDirectory
  Tasty.defaultMain $
    Tasty.testGroup "tests"
      [ Tasty.testGroup "singles" $
        foreach singleFiles $ \inputFile ->
          Tasty.testCase (drop (length singlesDirectory + 1) $ dropExtension inputFile) $ do
            checkFiles [takeDirectory inputFile] [inputFile]
      , Tasty.testGroup "multis" $
        foreach multiFiles $ \(dir, inputFiles) ->
          Tasty.testCase (drop (length multisDirectory + 1) dir) $
            checkFiles [dir] inputFiles
      ]

checkFiles :: [FileSystem.Directory] -> [FilePath] -> IO ()
checkFiles sourceDirectories files = do
  let
    prettyError err = do
      p <- Error.Hydrated.pretty err
      pure (err, p)
  (moduleSources, errs) <- Driver.runTask sourceDirectories (HashSet.fromList files) prettyError $
    forM files $ \filePath -> do
      (module_, _, defs) <- fetch $ Query.ParsedFile filePath
      let
        names =
          HashSet.fromList $
            Name.Qualified module_ . fst . snd <$> defs
      forM_ names $ \name -> do
        _type <- fetch $ Query.ElaboratedType name
        _maybeDef <- fetch $ Query.ElaboratedDefinition name
        pure ()
      moduleSource <- fetch $ Query.FileText filePath
      pure (filePath, moduleSource)

  forM_ moduleSources $ \(filePath, moduleSource) -> do
    let
      expectedErrors =
        expectedErrorsFromSource moduleSource

      moduleErrs =
        filter ((filePath ==) . Error.Hydrated._filePath . fst) errs
    verifyErrors filePath moduleErrs expectedErrors

verifyErrors :: FilePath -> [(Error.Hydrated, Doc ann)] -> HashMap Int ExpectedError -> IO ()
verifyErrors filePath errs expectedErrors = do
  let
    errorsMap =
      HashMap.fromList
        [ (Error.Hydrated.lineNumber err, errorToExpectedError $ Error.Hydrated._error err)
        | (err, _) <- errs
        ]

  forM_ (HashMap.toList expectedErrors) $ \(lineNumber, expectedError) ->
    case HashMap.lookup lineNumber errorsMap of
      Just expectedError'
        | expectedError == expectedError' ->
          pure ()

      _ ->
        Tasty.assertFailure $
          toS filePath <> ":" <> show (lineNumber + 1) <> ": " <>
          "Expected " <> show expectedError <> " error"

  forM_ errs $ \(err, doc) ->
    let
      failure =
        Tasty.assertFailure $
          "Unexpected error:\n" <> show (doc <> line)
    in
    case HashMap.lookup (Error.Hydrated.lineNumber err) expectedErrors of
      Just expectedError
        | expectedError == errorToExpectedError (Error.Hydrated._error err) ->
          pure ()

      _ ->
        failure

data ExpectedError
  = Parse
  | DuplicateName
  | ImportNotFound
  | MultipleFilesWithModuleName
  | ModuleFileNameMismatch
  | NotInScope
  | Ambiguous
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable
  | NonExhaustivePatterns
  | RedundantMatch
  | IndeterminateIndexUnification
  | PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch
  deriving (Eq, Show)

errorToExpectedError :: Error -> ExpectedError
errorToExpectedError err =
  case err of
    Error.Parse {} ->
      Parse

    Error.DuplicateName {} ->
      DuplicateName

    Error.ImportNotFound {} ->
      ImportNotFound

    Error.MultipleFilesWithModuleName {} ->
      MultipleFilesWithModuleName

    Error.ModuleFileNameMismatch {} ->
      ModuleFileNameMismatch

    Error.Elaboration _ (Error.Spanned _ elaborationError) ->
      case elaborationError of
        Error.NotInScope {} ->
          NotInScope

        Error.Ambiguous {} ->
          Ambiguous

        Error.TypeMismatch {} ->
          TypeMismatch

        Error.OccursCheck {} ->
          OccursCheck

        Error.UnsolvedMetaVariable {} ->
          UnsolvedMetaVariable

        Error.NonExhaustivePatterns {} ->
          NonExhaustivePatterns

        Error.RedundantMatch {} ->
          RedundantMatch

        Error.IndeterminateIndexUnification {} ->
          IndeterminateIndexUnification

        Error.PlicityMismatch {} ->
          PlicityMismatch

        Error.UnableToInferImplicitLambda {} ->
          UnableToInferImplicitLambda

        Error.ImplicitApplicationMismatch {} ->
          ImplicitApplicationMismatch

expectedErrorsFromSource
  :: Text
  -> HashMap Int ExpectedError
expectedErrorsFromSource sourceText =
  HashMap.fromList $ concatMap go $ zip [0..] $ Text.lines sourceText
  where
    go (lineNumber, lineText) =
      case Text.splitOn "--" lineText of
        [_, expectedErrorText] ->
          case Text.strip expectedErrorText of
            "parse error expected" ->
              [(lineNumber, Parse)]

            "duplicate name error expected" ->
              [(lineNumber, DuplicateName)]

            "import not found error expected" ->
              [(lineNumber, ImportNotFound)]

            "multiple files with module name error expected" ->
              [(lineNumber, ImportNotFound)]

            "module file name mismatch error expected" ->
              [(lineNumber, ImportNotFound)]

            "not in scope error expected" ->
              [(lineNumber, NotInScope)]

            "ambiguous name error expected" ->
              [(lineNumber, Ambiguous)]

            "type mismatch error expected" ->
              [(lineNumber, TypeMismatch)]

            "occurs check error expected" ->
              [(lineNumber, OccursCheck)]

            "unsolved meta error expected" ->
              [(lineNumber, UnsolvedMetaVariable)]

            "non-exhaustive patterns error expected" ->
              [(lineNumber, NonExhaustivePatterns)]

            "redundant match error expected" ->
              [(lineNumber, RedundantMatch)]

            "indeterminate index unification error expected" ->
              [(lineNumber, IndeterminateIndexUnification)]

            "plicity mismatch error expected" ->
              [(lineNumber, PlicityMismatch)]

            "unable to infer implicit lambda error expected" ->
              [(lineNumber, UnableToInferImplicitLambda)]

            "implicit application mismatch error expected" ->
              [(lineNumber, ImplicitApplicationMismatch)]

            _ ->
              mempty

        _ ->
          mempty

listDirectoryRecursive :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
listDirectoryRecursive p dir = do
  files <- listDirectory dir
  fmap concat $ forM files $ \file -> do
    let path = dir </> file
    isDir <- doesDirectoryExist path
    if isDir then
      listDirectoryRecursive p path

    else
      pure [path | p path]

listDirectoriesWithFilesMatching
  :: (FilePath -> Bool)
  -> FilePath
  -> IO [(FilePath, [FilePath])]
listDirectoriesWithFilesMatching p dir = do
  files <- listDirectory dir
  let
    paths = (dir </>) <$> files
  if any p paths then do
    recursiveFiles <- listDirectoryRecursive p dir
    pure [(dir, recursiveFiles)]

  else
    fmap concat $ forM paths $ \path -> do
      isDir <- doesDirectoryExist path
      if isDir then
        listDirectoriesWithFilesMatching p path

      else
        pure []
