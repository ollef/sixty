{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Error where

import Protolude

import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as Doc
import qualified Data.Text.Unsafe as Text

import qualified Meta
import Name (Name)
import qualified Name
import Plicity
import qualified Position
import qualified Scope
import qualified Span

data Error
  = Parse FilePath !Parsing
  | DuplicateName !Scope.KeyedName
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Ord, Show, Generic, Hashable)

data Elaboration
  = NotInScope !Name.Pre
  | Ambiguous !Name.Pre (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable !Meta.Index
  | NonExhaustivePatterns
  | OverlappingPatterns
  | PlicityMismatch !PlicityMismatch
  | UnableToInferImplicitLambda
  | ImplicitApplicationMismatch (HashMap Name ())
  deriving (Eq, Ord, Show, Generic, Hashable)

data PlicityMismatch
  = Mismatch !Plicity !Plicity
  | Missing !Plicity
  | Extra
  deriving (Eq, Ord, Show, Generic, Hashable)

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving (Eq, Ord, Show, Generic, Hashable)

data Parsing = Parsing
  { reason :: !(Maybe Text)
  , expected :: [Text]
  , position :: !Position.Absolute
  } deriving (Eq, Ord, Show, Generic, Hashable)

pretty :: FilePath -> Span.LineColumn -> Text -> Error -> Doc ann
pretty filePath span lineText err =
  Doc.pretty filePath <> ":" <> Doc.pretty span <> ":" <+> summary <> line <>
  spannedLine
  where
    summary =
      case err of
        Parse _ parse ->
          "Parse error" <+> Doc.pretty (reason parse)

        DuplicateName _ ->
          "Duplicate name"

        Elaboration _ (Error.Spanned _ err') ->
          case err' of
            NotInScope name ->
              "Not in scope:" <+> Doc.pretty name

            Ambiguous name constrCandidates nameCandidates ->
              "Ambiguous name:" <+> Doc.pretty name <> line <>
              "Candidates are:" <+>
                hcat (punctuate comma $
                  Doc.pretty <$> toList constrCandidates <|> Doc.pretty <$> toList nameCandidates)

            TypeMismatch ->
              "Type mismatch"

            OccursCheck ->
              "Failed occurs check"

            UnsolvedMetaVariable _ ->
              "Unsolved meta variable"

            NonExhaustivePatterns ->
              "Non-exhaustive patterns"

            OverlappingPatterns ->
              "Overlapping patterns"

            PlicityMismatch plicityMismatch ->
              case plicityMismatch of
                Mismatch expected_ actual ->
                  "Expected an " <> Doc.pretty expected_ <>
                  " but got an " <> Doc.pretty actual <>
                  " field"

                Missing expected_ ->
                  "Expected an " <> Doc.pretty expected_ <>
                  " field but didn't get any"

                Extra ->
                  "Unexpected field"

            UnableToInferImplicitLambda ->
              "Unable to infer implicit lambda"

            ImplicitApplicationMismatch _ ->
              "Unable to match implicit argument with type"

    spannedLine =
      let
        Span.LineColumns
          (Position.LineColumn startLineNumber startColumnNumber)
          (Position.LineColumn endLineNumber endColumnNumber) =
            span

        lineNumberText =
          show (startLineNumber + 1)

        lineNumberTextLength =
          Text.lengthWord16 lineNumberText

        (spanLength, spanEnding)
          | startLineNumber == endLineNumber =
            (endColumnNumber - startColumnNumber, mempty)
          | otherwise =
            (Text.lengthWord16 lineText - startColumnNumber, "...")
      in
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <> line <>
      Doc.pretty lineNumberText <> " | " <> Doc.pretty lineText <> line <>
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <>
      Doc.pretty (Text.replicate startColumnNumber " " <> "^" <> Text.replicate (spanLength - 1) "~" <> spanEnding)
