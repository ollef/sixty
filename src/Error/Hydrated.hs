{-# language OverloadedStrings #-}
module Error.Hydrated where

import Protolude

import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as Doc
import qualified Data.Text.Unsafe as Text
import Rock

import Error (Error)
import qualified Error
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

data Hydrated = Hydrated
  { _filePath :: FilePath
  , _lineColumn :: !Span.LineColumn
  , _lineText :: !Text
  , _error :: !Error
  } deriving Show

instance Pretty Hydrated where
  pretty h =
    Doc.pretty (_filePath h) <> ":" <> Doc.pretty (_lineColumn h) <> ":" <+> summary <> line <>
    spannedLine
    where
      summary =
        case _error h of
          Error.Parse _ parse ->
            "Parse error" <+> Doc.pretty (Error.reason parse)

          Error.DuplicateName (Scope.KeyedName _ name) ->
            "Duplicate name:" <+> Doc.pretty name

          Error.Elaboration _ (Error.Spanned _ err') ->
            case err' of
              Error.NotInScope name ->
                "Not in scope:" <+> Doc.pretty name

              Error.Ambiguous name constrCandidates nameCandidates ->
                "Ambiguous name:" <+> Doc.pretty name <> line <>
                "Candidates are:" <+>
                  hcat (punctuate comma $
                    Doc.pretty <$> toList constrCandidates <|> Doc.pretty <$> toList nameCandidates)

              Error.TypeMismatch ->
                "Type mismatch"

              Error.OccursCheck ->
                "Failed occurs check"

              Error.UnsolvedMetaVariable _ ->
                "Unsolved meta variable"

              Error.NonExhaustivePatterns ->
                "Non-exhaustive patterns"

              Error.OverlappingPatterns ->
                "Overlapping patterns"

              Error.PlicityMismatch plicityMismatch ->
                case plicityMismatch of
                  Error.Mismatch expected_ actual ->
                    "Expected an " <> Doc.pretty expected_ <>
                    " but got an " <> Doc.pretty actual <>
                    " field"

                  Error.Missing expected_ ->
                    "Expected an " <> Doc.pretty expected_ <>
                    " field but didn't get any"

                  Error.Extra ->
                    "Unexpected field"

              Error.UnableToInferImplicitLambda ->
                "Unable to infer implicit lambda"

              Error.ImplicitApplicationMismatch _ ->
                "Unable to match implicit argument with type"

      spannedLine =
        let
          Span.LineColumns
            (Position.LineColumn startLineNumber startColumnNumber)
            (Position.LineColumn endLineNumber endColumnNumber) =
              _lineColumn h

          lineNumberText =
            show (startLineNumber + 1)

          lineNumberTextLength =
            Text.lengthWord16 lineNumberText

          (spanLength, spanEnding)
            | startLineNumber == endLineNumber =
              (endColumnNumber - startColumnNumber, mempty)
            | otherwise =
              (Text.lengthWord16 (_lineText h) - startColumnNumber, "...")
        in
        Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <> line <>
        Doc.pretty lineNumberText <> " | " <> Doc.pretty (_lineText h) <> line <>
        Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <>
        Doc.pretty (Text.replicate startColumnNumber " " <> "^" <> Text.replicate (spanLength - 1) "~" <> spanEnding)

fromError :: Error -> Task Query Hydrated
fromError err = do
  (filePath, span) <- fetch $ Query.ErrorSpan err
  text <- fetch $ Query.FileText filePath
  let
    trimmedSpan =
      Span.trim text span
    (lineColumn, lineText) =
      Span.lineColumn trimmedSpan text
  pure Hydrated
    { _filePath = filePath
    , _lineColumn = lineColumn
    , _lineText = lineText
    , _error = err
    }

lineNumber :: Hydrated -> Int
lineNumber err =
  l
  where
    Span.LineColumns (Position.LineColumn l _) _ =
      _lineColumn err
