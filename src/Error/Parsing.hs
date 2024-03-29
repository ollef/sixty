{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Error.Parsing where

import qualified Position
import Protolude

data Parsing = Parsing
  { reason :: !(Maybe Text)
  , expected :: [Text]
  , position :: Either EOF Position.Absolute
  }
  deriving (Eq, Ord, Show, Generic, Hashable)

data EOF = EOF
  deriving (Eq, Ord, Show, Generic, Hashable)
