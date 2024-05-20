{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Low.PassBy where

import Low.Representation (Representation)
import Protolude

data PassBy
  = Value !Representation
  | Reference
  deriving (Eq, Show, Generic, Hashable)
