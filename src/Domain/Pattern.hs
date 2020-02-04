module Domain.Pattern where

import Protolude

import Literal (Literal)
import qualified Name
import Plicity

data Pattern
  = Wildcard
  | Con !Name.QualifiedConstructor [(Plicity, Pattern)]
  | Lit !Literal
  deriving (Eq, Show)
