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
import qualified Name
import qualified Position
import qualified Query
import qualified Span

main :: IO ()
main = do
  let
    singlesDirectory =
      "tests/singles/"

    multisDirectory =
      "tests/multis/"

    isSourceFile =
      (== ".lx") . takeExtension

  singleFiles <- listDirectoryRecursive isSourceFile singlesDirectory
  multiFiles <- listDirectoriesWithFilesMatching isSourceFile multisDirectory
  Tasty.defaultMain $
    Tasty.testGroup "tests"
      [ Tasty.testGroup "singles" $
        foreach singleFiles $ \inputFile ->
          Tasty.testCase (drop (length singlesDirectory) $ dropExtension inputFile) $
            checkFiles [inputFile]
      , Tasty.testGroup "multis" $
        foreach multiFiles $ \(dir, inputFiles) ->
          Tasty.testCase (drop (length multisDirectory) dir) $
            checkFiles inputFiles
      ]

checkFiles :: [FilePath] -> IO ()
checkFiles files = do
  (moduleSources, errs) <- Driver.runTask files $
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
        filter (\(errFilePath, _, _, _) -> filePath == errFilePath) errs
    verifyErrors filePath moduleErrs expectedErrors

verifyErrors :: FilePath -> [(FilePath, Span.LineColumn, Text, Error)] -> HashMap Int ExpectedError -> IO ()
verifyErrors filePath errs expectedErrors = do
  let
    errorsMap =
      HashMap.fromList
        [ (lineNumber, errorToExpectedError err)
        | (_, Span.LineColumns (Position.LineColumn lineNumber _) _, _, err) <- errs
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

  forM_ errs $ \(errFilePath, lineColumn@(Span.LineColumns (Position.LineColumn lineNumber _) _), lineText, err) ->
    let
      failure =
        Tasty.assertFailure $
          "Unexpected error:\n" <> show (Error.pretty errFilePath lineColumn lineText err <> line)
    in
    case HashMap.lookup lineNumber expectedErrors of
      Just expectedError
        | expectedError == errorToExpectedError err ->
          pure ()

      _ ->
        failure

data ExpectedError
  = Parse
  | DuplicateName
  | NotInScope
  | Ambiguous
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable
  | NonExhaustivePatterns
  | OverlappingPatterns
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

        Error.OverlappingPatterns {} ->
          OverlappingPatterns

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

            "overlapping patterns error expected" ->
              [(lineNumber, OverlappingPatterns)]

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
