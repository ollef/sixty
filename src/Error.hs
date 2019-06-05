{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Error where

import Protolude

import Data.Text.Prettyprint.Doc as Doc

import qualified Meta
import qualified Position
import qualified Presyntax
import qualified Scope
import qualified Span

data Error
  = Parse !Parsing
  | DuplicateName !Scope.KeyedName
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving (Eq, Ord, Show, Generic, Hashable)

data Elaboration
  = NotInScope !Presyntax.Name
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
  , file :: !FilePath
  } deriving (Eq, Ord, Show, Generic, Hashable)

pretty :: FilePath -> Span.LineColumn -> Error -> Doc ann
pretty filePath span err =
  Doc.pretty filePath <> ":" <> Doc.pretty span <> ":" <+>
  case err of
    Parse _ ->
      "Parse error"

    DuplicateName _ ->
      "Duplicate name"

    Elaboration _ (Error.Spanned _ err') ->
      case err' of
        NotInScope (Presyntax.Name name) ->
          "Not in scope:" <+> Doc.pretty name

        TypeMismatch ->
          "Type mismatch"

        OccursCheck ->
          "Failed occurs check"

        UnsolvedMetaVariable _ ->
          "Unsolved meta variable"
