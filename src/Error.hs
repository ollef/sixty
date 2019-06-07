{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Error where

import Protolude

import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as Doc
import qualified Data.Text.Unsafe as Text

import qualified Meta
import qualified Name
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
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable !Meta.Index
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
            NotInScope (Name.Pre name) ->
              "Not in scope:" <+> Doc.pretty name

            TypeMismatch ->
              "Type mismatch"

            OccursCheck ->
              "Failed occurs check"

            UnsolvedMetaVariable _ ->
              "Unsolved meta variable"

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
