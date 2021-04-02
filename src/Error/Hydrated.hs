{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Error.Hydrated where

import Protolude hiding (moduleName)

import qualified Data.ByteString as ByteString
import Data.Coerce
import Data.Persist
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as Doc
import Rock
import qualified System.Directory as Directory

import qualified Core.Pretty as Pretty
import Error (Error)
import qualified Error
import qualified Error.Parsing
import qualified Module
import Name (Name)
import qualified Name
import Plicity
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

data Hydrated = Hydrated
  { _filePath :: FilePath
  , _lineColumn :: !Span.LineColumn
  , _lineText :: !ByteString
  , _error :: !Error
  } deriving (Show, Generic, Persist)

headingAndBody :: (MonadFetch Query m, MonadIO m) => Error -> m (Doc ann, Doc ann)
headingAndBody error =
  case error of
    Error.Parse _ parse ->
      pure
        ("Parse error"
        , Doc.pretty (Error.Parsing.reason parse) <>
          case Error.Parsing.expected parse of
            [] ->
              mempty

            expected ->
              line <> "Expected: " <> hcat (punctuate comma $ Doc.pretty <$> expected)
        )

    Error.DuplicateName keyedName@(Scope.KeyedName _ name) _span -> do
      (filePath, oldSpan) <- fetch $ Query.KeyedNamePosition keyedName
      text <- fetch $ Query.FileText filePath
      let
        (lineColumn, _) =
          Position.lineColumn oldSpan text
      pure
        ( "Duplicate name:" <+> Doc.pretty name
        , Doc.pretty name <+> "has already been defined at" <+> Doc.pretty (Span.LineColumns lineColumn lineColumn) <> "."
        )

    Error.ImportNotFound _ import_ ->
      let
        prettyModule =
          Doc.pretty (Module._module import_)
      in
      pure
        ( "Module not found:" <+> prettyModule
        , "The imported module" <+> prettyModule <+> "wasn't found in the current project."
        )

    Error.MultipleFilesWithModuleName moduleName file1 file2 -> do
      file1' <- liftIO $ Directory.makeRelativeToCurrentDirectory file1
      file2' <- liftIO $ Directory.makeRelativeToCurrentDirectory file2
      pure
        ( "Multiple files use the module name" <+> Doc.pretty moduleName
        , "Both" <> line <>
          indent 2 (Doc.pretty file1') <> line <>
          "and" <> line <>
          indent 2 (Doc.pretty file2') <> line <>
          "use the same module name."
        )

    Error.ModuleFileNameMismatch givenModuleName expectedModuleName _ _ ->
      pure
        ( "Module name doesn't match file name"
        , "The module name given in the module header is" <> line <>
          indent 2 (Doc.pretty givenModuleName) <> line <>
          "but from the file's location I expected it to be" <> line <>
          indent 2 (Doc.pretty expectedModuleName) <> "."
        )

    Error.Elaboration keyedName (Error.Spanned _ err') ->
      case err' of
        Error.NotInScope name ->
          pure
            ( "Not in scope:" <+> Doc.pretty name
            , Doc.pretty name <+> "is not defined here."
            )

        Error.Ambiguous name constrCandidates nameCandidates ->
          pure
            ("Ambiguous name:" <+> Doc.pretty name
            , "Candidates are:" <+>
              hcat
                (punctuate comma $
                  Doc.pretty <$> toList constrCandidates <|> Doc.pretty <$> toList nameCandidates
                )
            )

        Error.DuplicateLetName name previousSpan -> do
          (filePath, defSpan) <- fetch $ Query.KeyedNamePosition keyedName
          text <- fetch $ Query.FileText filePath
          let
            (previousLineColumn, _) =
              Span.lineColumn (Span.absoluteFrom defSpan previousSpan) text
          pure
            ( "Duplicate name in let block:" <+> Doc.pretty name
            , Doc.pretty name <+> "has already been defined at" <+> Doc.pretty previousLineColumn <> "."
            )

        Error.UndefinedLetName name ->
          pure
            ( "Undefined name in let block:" <+> Doc.pretty name
            , "The type of" <+> Doc.pretty name <+> "was declared here, but not its value."
            )

        Error.TypeMismatch mismatches -> do
          mismatches' <- forM mismatches $ \(inferred, expected) -> do
            inferred' <- prettyPrettyableTerm 0 inferred
            expected' <- prettyPrettyableTerm 0 expected
            pure (inferred', expected')
          pure
            ( "Type mismatch"
            , vcat
                (intercalate ["", "while trying to unify"]
                  [ [ "Inferred:" <+> inferred
                    , "Expected:" <+> expected
                    ]
                  | (inferred, expected) <- toList mismatches'
                  ]
                )
            )

        Error.OccursCheck mismatches -> do
          mismatches' <- forM mismatches $ \(inferred, expected) -> do
            inferred' <- prettyPrettyableTerm 0 inferred
            expected' <- prettyPrettyableTerm 0 expected
            pure (inferred', expected')
          pure
            ( "Occurs check failed"
            , vcat
                (intercalate ["", "while trying to unify"]
                  [ [ "Inferred:" <+> inferred
                    , "Expected:" <+> expected
                    ]
                  | (inferred, expected) <- toList mismatches'
                  ]
                )
              <> line <> line <>
              "Unifying these values would produce a cyclic term."
            )

        Error.UnsolvedMetaVariable index type_ -> do
          type' <- prettyPrettyableTerm 0 type_
          pure
            ( "Unsolved meta variable"
            , "A meta variable was created here but was never solved:" <> line <> line <>
              Doc.pretty index <+> ":" <+> type'
            )

        Error.NonExhaustivePatterns patterns -> do
          prettyPatterns <- mapM (mapM $ prettyPrettyablePattern $ Pretty.appPrec + 1) patterns
          pure
            ( "Non-exhaustive patterns"
            , "Patterns not matched:" <> line <> line <>
              vcat (hsep <$> prettyPatterns)
            )

        Error.RedundantMatch matchKind ->
          pure ("Redundant" <+> Doc.pretty matchKind, "This" <+> Doc.pretty matchKind <+> "is unreachable")

        Error.IndeterminateIndexUnification fieldOrArg ->
          pure
            ( "Indeterminate index unification"
            , "I don't know whether this" <+> Doc.pretty fieldOrArg <+>
              "applies or not, because the unification of a constructor type's indices failed to produce a definite result."
            )

        Error.PlicityMismatch fieldOrArg plicityMismatch ->
          pure $ case plicityMismatch of
            Error.Mismatch expected_ actual ->
              ( "Plicity mismatch"
              , "Expected an" <+> Doc.pretty expected_ <+> Doc.pretty fieldOrArg <+>
                "but got an" <+> Doc.pretty actual <+> Doc.pretty fieldOrArg
              )

            Error.Missing expected_ ->
              ( "Missing" <+> Doc.pretty fieldOrArg
              , "Expected an" <+> Doc.pretty expected_ <+> Doc.pretty fieldOrArg <+>
                "but didn't get any"
              )

            Error.Extra ->
              ( "Unexpected" <+> Doc.pretty fieldOrArg
              , "Didn't expect a" <+> Doc.pretty fieldOrArg <+> "here"
              )

        Error.UnableToInferImplicitLambda ->
          pure ("Unable to infer implicit lambda", mempty)

        Error.ImplicitApplicationMismatch names term type_ -> do
          term' <- prettyPrettyableTerm 0 term
          type' <- prettyPrettyableTerm 0 type_
          pure
            ( "Plicity mismatch"
            , "The term" <> line <> line <>
              indent 4 term' <> line <> line <>
              "doesn't accept implicit arguments named" <> line <> line <>
              indent 4 (hcat $ punctuate comma $ Doc.pretty <$> toList names) <> line <> line <>
              "Its type is:" <> line <> line <> type'
            )

pretty :: (MonadFetch Query m, MonadIO m) => Hydrated -> m (Doc ann)
pretty h = do
  filePath <- liftIO $ Directory.makeRelativeToCurrentDirectory $ _filePath h
  (heading, body) <- headingAndBody $ _error h
  pure $
    Doc.pretty filePath <> ":" <> Doc.pretty (_lineColumn h) <> ":" <+> heading <> line <> line <>
    body <> line <> line <>
    spannedLine
  where
    spannedLine =
      let
        Span.LineColumns
          (Position.LineColumn startLineNumber startColumnNumber)
          (Position.LineColumn endLineNumber endColumnNumber) =
            _lineColumn h

        lineNumberText =
          encodeUtf8 $ show (startLineNumber + 1)

        lineNumberTextLength =
          ByteString.length lineNumberText

        (spanLength, spanEnding)
          | startLineNumber == endLineNumber =
            (endColumnNumber - startColumnNumber, mempty)
          | otherwise =
            (ByteString.length (_lineText h) - startColumnNumber, "...")
      in
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <> line <>
      Doc.pretty (decodeUtf8 lineNumberText) <> " | " <> Doc.pretty (decodeUtf8 $ _lineText h) <> line <>
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <>
      Doc.pretty (Text.replicate startColumnNumber " " <> "^" <> Text.replicate (spanLength - 1) "~" <> spanEnding)

fromError :: Error -> Task Query Hydrated
fromError err = do
  (filePath, eofOrSpan) <-
    case err of
      Error.Parse filePath parseError ->
        pure
          ( filePath
          , (\p -> Span.Absolute p p) <$> Error.Parsing.position parseError
          )

      Error.DuplicateName (Scope.KeyedName _ (Name.Qualified module_ _)) span -> do
        maybeModuleFile <- fetch $ Query.ModuleFile module_
        pure (fromMaybe "<no file>" maybeModuleFile, Right span)

      Error.ImportNotFound module_ import_ -> do
        maybeModuleFile <- fetch $ Query.ModuleFile module_
        pure (fromMaybe "<no file>" maybeModuleFile, Right $ Module._span import_)

      Error.MultipleFilesWithModuleName _ _ file2 ->
        pure (file2, Right $ Span.Absolute 0 0)

      Error.ModuleFileNameMismatch _ _ span file ->
        pure (file, Right span)

      Error.Elaboration keyedName (Error.Spanned relativeSpan _) -> do
        (file, absolutePosition) <- fetch $ Query.KeyedNamePosition keyedName
        pure (file, Right $ Span.absoluteFrom absolutePosition relativeSpan)
  text <- fetch $ Query.FileText filePath
  let
    (lineColumn, lineText) =
      case eofOrSpan of
        Left Error.Parsing.EOF -> do
          let
            eofPos =
              Position.Absolute $ ByteString.length text
          Span.lineColumn (Span.Absolute eofPos eofPos) text

        Right span ->
          Span.lineColumn span text
  pure Hydrated
    { _filePath = filePath
    , _lineColumn = lineColumn
    , _lineText = lineText
    , _error = err
    }

-------------------------------------------------------------------------------

lineNumber :: Hydrated -> Int
lineNumber err =
  l
  where
    Span.LineColumns (Position.LineColumn l _) _ =
      _lineColumn err

prettyPrettyableTerm :: MonadFetch Query m => Int -> Error.PrettyableTerm -> m (Doc ann)
prettyPrettyableTerm prec (Error.PrettyableTerm moduleName_ names term) = do
  env <- Pretty.emptyM moduleName_
  pure $ go names env
  where
    go :: [Name] -> Pretty.Environment v -> Doc ann
    go names' env' =
      case names' of
        [] ->
          Pretty.prettyTerm prec (coerce env') term

        name:names'' ->
          let
            (env'', _) =
              Pretty.extend env' name
          in
          go names'' env''

prettyPrettyablePattern :: MonadFetch Query m => Int -> (Plicity, Error.PrettyablePattern) -> m (Doc ann)
prettyPrettyablePattern prec (plicity, Error.PrettyablePattern moduleName_ names pattern_) = do
  env <- Pretty.emptyM moduleName_
  pure $ go names env
  where
    go :: [Name] -> Pretty.Environment v -> Doc ann
    go names' env' =
      case names' of
        [] ->
          Plicity.prettyAnnotation plicity <> Pretty.prettyPattern prec env' pattern_

        name:names'' ->
          let
            (env'', _) =
              Pretty.extend env' name

          in
          go names'' env''
