{-# language OverloadedStrings #-}
module Main where

import Protolude

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
  ((), errs) <- Driver.runTask $ do
    defs <- fetch $ Query.ParsedModule module_
    let
      names =
        HashSet.fromList $
          Name.Qualified module_ . fst . snd <$> defs
    forM_ names $ \name -> do
      _type <- fetch $ Query.ElaboratedType name
      _maybeDef <- fetch $ Query.ElaboratedDefinition name
      pure ()
  -- TODO: Also check that the set of expected errors doesn't
  -- contain errors that we _don't_ get.
  verifyErrors errs

verifyErrors :: [(FilePath, Span.LineColumn, Text, Error)] -> IO ()
verifyErrors errs =
  forM_ errs $ \(filePath, lineColumn, lineText, err) ->
    let
      failure =
        Tasty.assertFailure $ show $ Error.pretty filePath lineColumn lineText err <> line
    in
    case Text.splitOn "--" lineText of
      [_, expectedErrorText] ->
        case (err, Text.strip expectedErrorText) of
          (Error.Parse {}, "parse error expected") ->
            pure ()

          (Error.Parse {}, _) ->
            failure

          (Error.DuplicateName {}, "duplicate name error expected") ->
            pure ()

          (Error.DuplicateName {}, _) ->
            failure

          (Error.Elaboration _ (Error.Spanned _ elaborationError), strippedExpectedErrorText) ->
            case (elaborationError, strippedExpectedErrorText) of
              (Error.NotInScope {}, "not in scope error expected") ->
                pure ()

              (Error.NotInScope {}, _) ->
                failure

              (Error.Ambiguous {}, "ambiguous name error expected") ->
                pure ()

              (Error.Ambiguous {}, _) ->
                failure

              (Error.TypeMismatch {}, "type mismatch error expected") ->
                pure ()

              (Error.TypeMismatch {}, _) ->
                failure

              (Error.OccursCheck {}, "occurs check error expected") ->
                pure ()

              (Error.OccursCheck {}, _) ->
                failure

              (Error.UnsolvedMetaVariable {}, "unsolved meta error expected") ->
                pure ()

              (Error.UnsolvedMetaVariable {}, _) ->
                failure

      _ ->
        failure


listDirectoryRecursive :: FilePath -> (FilePath -> Bool) -> IO [FilePath]
listDirectoryRecursive dir p = do
  files <- listDirectory dir
  fmap concat $ forM files $ \file -> do
    let path = dir </> file
    isDir <- doesDirectoryExist path
    if isDir then
      listDirectoryRecursive path p

    else
      return [path | p path]
