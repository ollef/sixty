{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Boxity where

import Data.Persist
import Prettyprinter
import Protolude

data Boxity
  = Unboxed
  | Boxed
  deriving (Eq, Ord, Show, Generic, Persist, Hashable)

instance Pretty Boxity where
  pretty boxity =
    case boxity of
      Unboxed ->
        "unboxed"
      Boxed ->
        "boxed"

prettyAnnotation :: Boxity -> Doc ann -> Doc ann
prettyAnnotation boxity =
  case boxity of
    Unboxed ->
      identity
    Boxed ->
      ("boxed" <+>)
