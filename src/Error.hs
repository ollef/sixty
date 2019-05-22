module Error where

import Protolude

import qualified Text.Parsix as Parsix

import Name (Name)
import qualified Presyntax

data Error
  = Parse !Parsix.Error
  | DuplicateName !Name
  | NotInScope !Presyntax.Name
  deriving Show
