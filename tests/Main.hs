{-# language OverloadedStrings #-}
module Main where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.String
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
    inputDirectory =
      "tests/input/"
  inputFiles <- listDirectoryRecursive inputDirectory $ (== ".lx") . takeExtension
  Tasty.defaultMain $
    Tasty.testGroup "Test files" $
      foreach inputFiles $ \inputFile -> do
        let
          inputModule = dropExtension inputFile
        Tasty.testCase (drop (length inputDirectory) inputModule) $
          checkModule (fromString inputModule)

checkModule :: Name.Module -> IO ()
checkModule module_ = do
  (moduleSource, errs) <- Driver.runTask $ do
    defs <- fetch $ Query.ParsedModule module_
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . fst . snd <$> defs
    forM_ names $ \name -> do
      _type <- fetch $ Query.ElaboratedType name
      _maybeDef <- fetch $ Query.ElaboratedDefinition name
      pure ()
    fetch $ Query.ReadFile $ Query.moduleFilePath module_

  let
    expectedErrors =
      expectedErrorsFromSource moduleSource
  verifyErrors errs expectedErrors

verifyErrors :: [(FilePath, Span.LineColumn, Text, Error)] -> HashMap Int ExpectedError -> IO ()
verifyErrors errs expectedErrors = do
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
          "Expected " <> show expectedError <> " error on line " <> show lineNumber

  forM_ errs $ \(filePath, lineColumn@(Span.LineColumns (Position.LineColumn lineNumber _) _), lineText, err) ->
    let
      failure =
        Tasty.assertFailure $
          "Unexpected error:\n" <> show (Error.pretty filePath lineColumn lineText err <> line)
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
  | PlicityMismatch
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

        Error.PlicityMismatch {} ->
          PlicityMismatch

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

            "plicity mismatch error expected" ->
              [(lineNumber, PlicityMismatch)]

            _ ->
              mempty

        _ ->
          mempty

listDirectoryRecursive :: FilePath -> (FilePath -> Bool) -> IO [FilePath]
listDirectoryRecursive dir p = do
  files <- listDirectory dir
  fmap concat $ forM files $ \file -> do
    let path = dir </> file
    isDir <- doesDirectoryExist path
    if isDir then
      listDirectoryRecursive path p

    else
      pure [path | p path]
