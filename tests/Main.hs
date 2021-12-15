{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Command.Compile
import qualified Compiler
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.String (String)
import qualified Data.Text as Text
import qualified Driver
import Error (Error)
import qualified Error
import qualified Error.Hydrated
import qualified Error.Hydrated as Error (Hydrated)
import qualified FileSystem
import Prettyprinter
import Protolude
import qualified Query
import Rock
import System.Directory
import System.FilePath
import System.Process
import qualified Test.Tasty as Tasty
import qualified Test.Tasty.HUnit as Tasty

main :: IO ()
main = do
  singlesDirectory <- canonicalizePath "tests/singles"
  multisDirectory <- canonicalizePath "tests/multis"
  compilationDirectory <- canonicalizePath "tests/compilation"

  let isSourceFile =
        (== ".vix") . takeExtension

  singleFiles <- listDirectoryRecursive isSourceFile singlesDirectory
  multiFiles <- listDirectoriesWithFilesMatching isSourceFile multisDirectory
  compilationFiles <- listDirectoryRecursive isSourceFile compilationDirectory
  Tasty.defaultMain $
    Tasty.testGroup
      "tests"
      [ Tasty.testGroup "singles" $
          foreach singleFiles $ \inputFile ->
            Tasty.testCase (drop (length singlesDirectory + 1) $ dropExtension inputFile) $
              checkFiles [takeDirectory inputFile] [inputFile]
      , Tasty.testGroup "multis" $
          foreach multiFiles $ \(dir, inputFiles) ->
            Tasty.testCase (drop (length multisDirectory + 1) dir) $
              checkFiles [dir] inputFiles
      , Tasty.testGroup "compilation" $
          foreach compilationFiles $ \inputFile ->
            Tasty.testCase (drop (length compilationDirectory + 1) $ dropExtension inputFile) $
              compileFiles Nothing [takeDirectory inputFile] [inputFile]
      , Tasty.testGroup "optimised compilation" $
          foreach compilationFiles $ \inputFile ->
            Tasty.testCase (drop (length compilationDirectory + 1) $ dropExtension inputFile) $
              compileFiles (Just "2") [takeDirectory inputFile] [inputFile]
      ]

checkFiles :: [FileSystem.Directory] -> [FilePath] -> IO ()
checkFiles sourceDirectories files = do
  let prettyError err = do
        p <- Error.Hydrated.pretty err
        pure (err, p)
  (moduleSources, errs) <- Driver.runTask (HashSet.fromList sourceDirectories) (HashSet.fromList files) prettyError $ do
    Driver.checkAll
    forM files $ \filePath -> do
      moduleSource <- fetch $ Query.FileText filePath
      pure (filePath, moduleSource)

  forM_ moduleSources $ \(filePath, moduleSource) -> do
    let expectedErrors =
          expectedErrorsFromSource moduleSource

        moduleErrs =
          filter ((filePath ==) . Error.Hydrated._filePath . fst) errs
    verifyErrors filePath moduleErrs expectedErrors

compileFiles :: Maybe String -> [FileSystem.Directory] -> [FilePath] -> IO ()
compileFiles optimisationLevel sourceDirectories files = do
  let prettyError err = do
        p <- Error.Hydrated.pretty err
        pure (err, p)
  Command.Compile.withOutputFile Nothing $ \outputExecutableFile ->
    Command.Compile.withAssemblyDirectory Nothing $ \assemblyDir -> do
      (moduleSources, errs) <- Driver.runTask (HashSet.fromList sourceDirectories) (HashSet.fromList files) prettyError $ do
        Driver.checkAll
        Compiler.compile assemblyDir False outputExecutableFile optimisationLevel
        forM files $ \filePath -> do
          moduleSource <- fetch $ Query.FileText filePath
          pure (filePath, moduleSource)

      executableOutput <- readProcess outputExecutableFile [] []
      forM_ moduleSources $ \(filePath, moduleSource) -> do
        let expectedErrors =
              expectedErrorsFromSource moduleSource

            moduleErrs =
              filter ((filePath ==) . Error.Hydrated._filePath . fst) errs
        verifyErrors filePath moduleErrs expectedErrors
        let expectedOutput = expectedOutputFromSource moduleSource
        unless (null expectedOutput) $ do
          verifyExecutableOutput filePath (toS executableOutput) $ Text.unlines expectedOutput

verifyErrors :: FilePath -> [(Error.Hydrated, Doc ann)] -> HashMap Int [ExpectedError] -> IO ()
verifyErrors filePath errs expectedErrors = do
  let errorsMap =
        HashMap.fromListWith
          (<>)
          [ (Error.Hydrated.lineNumber err, pure $ errorToExpectedError $ Error.Hydrated._error err)
          | (err, _) <- errs
          ]

  forM_ (HashMap.toList expectedErrors) $ \(lineNumber, expectedErrorsOnLine) ->
    case HashMap.lookup lineNumber errorsMap of
      Just errorsOnLine
        | sort errorsOnLine == sort expectedErrorsOnLine ->
          pure ()
      maybeErrorsOnLine ->
        Tasty.assertFailure $
          toS filePath <> ":" <> show (lineNumber + 1) <> ": "
            <> "Expected "
            <> show expectedErrorsOnLine
            <> " errors, got "
            <> show (fold maybeErrorsOnLine)

  forM_ errs $ \(err, doc) ->
    case HashMap.lookup (Error.Hydrated.lineNumber err) expectedErrors of
      Just expectedErrorsOnLine
        | errorToExpectedError (Error.Hydrated._error err) `elem` expectedErrorsOnLine ->
          pure ()
      _ ->
        Tasty.assertFailure $
          "Unexpected error:\n" <> show (doc <> line)

data ExpectedError
  = Parse
  | DuplicateName
  | ImportNotFound
  | MultipleFilesWithModuleName
  | ModuleFileNameMismatch
  | NotInScope
  | Ambiguous
  | DuplicateLetName
  | UndefinedLetName
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable
  | NonExhaustivePatterns
  | RedundantMatch
  | IndeterminateIndexUnification
  | PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch
  deriving (Eq, Ord, Show)

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
    Error.Elaboration _ _ (Error.Spanned _ elaborationError) ->
      case elaborationError of
        Error.NotInScope {} ->
          NotInScope
        Error.Ambiguous {} ->
          Ambiguous
        Error.DuplicateLetName {} ->
          DuplicateLetName
        Error.UndefinedLetName {} ->
          UndefinedLetName
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

expectedErrorsFromSource :: Text -> HashMap Int [ExpectedError]
expectedErrorsFromSource sourceText =
  HashMap.fromListWith (<>) $ concatMap (map (second pure) . go) $ zip [0 ..] $ Text.lines sourceText
  where
    go (lineNumber, lineText) =
      case Text.splitOn "--" lineText of
        [_, expectedErrorTexts] -> do
          expectedErrorText <- Text.splitOn "," expectedErrorTexts
          case Text.strip expectedErrorText of
            "parse error expected" ->
              [(lineNumber, Parse)]
            "duplicate name error expected" ->
              [(lineNumber, DuplicateName)]
            "import not found error expected" ->
              [(lineNumber, ImportNotFound)]
            "multiple files with module name error expected" ->
              [(lineNumber, MultipleFilesWithModuleName)]
            "module file name mismatch error expected" ->
              [(lineNumber, ModuleFileNameMismatch)]
            "not in scope error expected" ->
              [(lineNumber, NotInScope)]
            "ambiguous name error expected" ->
              [(lineNumber, Ambiguous)]
            "duplicate let name error expected" ->
              [(lineNumber, DuplicateLetName)]
            "undefined let name error expected" ->
              [(lineNumber, UndefinedLetName)]
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

verifyExecutableOutput :: FilePath -> Text -> Text -> IO ()
verifyExecutableOutput filePath output expectedOutput =
  when (output /= expectedOutput) $
    Tasty.assertFailure $
      toS filePath <> ":\n"
        <> "Expected output:\n\n"
        <> toS expectedOutput
        <> "\nbut got:\n\n"
        <> toS output

expectedOutputFromSource :: Text -> [Text]
expectedOutputFromSource sourceText =
  concatMap go $ Text.lines sourceText
  where
    go lineText =
      case Text.splitOn "-- prints " lineText of
        [_, expectedOutput] ->
          [expectedOutput]
        _ ->
          []

listDirectoryRecursive :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
listDirectoryRecursive p dir = do
  files <- listDirectory dir
  fmap concat $
    forM files $ \file -> do
      let path = dir </> file
      isDir <- doesDirectoryExist path
      if isDir
        then listDirectoryRecursive p path
        else pure [path | p path]

listDirectoriesWithFilesMatching ::
  (FilePath -> Bool) ->
  FilePath ->
  IO [(FilePath, [FilePath])]
listDirectoriesWithFilesMatching p dir = do
  files <- listDirectory dir
  let paths = (dir </>) <$> files
  if any p paths
    then do
      recursiveFiles <- listDirectoryRecursive p dir
      pure [(dir, recursiveFiles)]
    else fmap concat $
      forM paths $ \path -> do
        isDir <- doesDirectoryExist path
        if isDir
          then listDirectoriesWithFilesMatching p path
          else pure []
