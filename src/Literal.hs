{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Literal where

import Protolude

import Data.Text.Prettyprint.Doc

newtype Literal
  = Integer Integer
  deriving (Eq, Generic, Hashable, Show)

instance Pretty Literal where
  pretty literal =
    case literal of
      Literal.Integer int ->
        pretty int
