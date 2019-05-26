module Error where

import Protolude

import qualified Text.Parsix as Parsix

import qualified Meta
import Name (Name)
import qualified Name
import qualified Presyntax

data Error
  = Parse !Parsix.Error
  | DuplicateName !Name
  | NotInScope !Presyntax.Name
  | TypeMismatch
  | OccursCheck
  | UnsolvedMetaVariable !Name.Qualified !Meta.Index
  deriving Show
