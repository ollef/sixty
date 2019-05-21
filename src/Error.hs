module Error where

import Protolude

import qualified Text.Parsix as Parsix

import Name (Name)

data Error
  = Parse !Parsix.Error
  | DuplicateName !Name
  deriving Show
