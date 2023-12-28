{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Literal where

import Prettyprinter
import Protolude

newtype Literal
  = Integer Integer
  deriving (Eq, Generic, Show, Hashable)

instance Pretty Literal where
  pretty literal =
    case literal of
      Literal.Integer int ->
        pretty int
