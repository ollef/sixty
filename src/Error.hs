module Error where

import Protolude

import qualified Text.Parsix as Parsix

import qualified Meta
import qualified Presyntax
import qualified Scope
import qualified Span

data Error
  = Parse !Parsix.Error
  | DuplicateName !Scope.KeyedName
  | Elaboration !Scope.KeyedName !Error.Spanned
  deriving Show

data Elaboration
  = NotInScope !Presyntax.Name
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable !Meta.Index
  deriving Show

data Spanned
  = Spanned !Span.Relative !Error.Elaboration
  deriving Show
