{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Core.Domain.Pattern where

import Literal (Literal)
import qualified Name
import Plicity
import Protolude

data Pattern
  = Wildcard
  | Con !Name.QualifiedConstructor [(Plicity, Pattern)]
  | Lit !Literal
  deriving (Eq, Show, Generic)
