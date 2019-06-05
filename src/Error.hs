{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Error where

import Protolude

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
