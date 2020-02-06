{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Error.Parsing where

import Protolude

import Data.Persist

import qualified Position

data Parsing = Parsing
  { reason :: !(Maybe Text)
  , expected :: [Text]
  , position :: !Position.Absolute
  } deriving (Eq, Ord, Show, Generic, Persist, Hashable)
