{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Span where

import Protolude

import qualified Position

data Absolute = Absolute !Position.Absolute !Position.Absolute
  deriving (Eq, Ord, Show, Generic, Hashable)

data Relative = Relative !Position.Relative !Position.Relative
  deriving (Eq, Ord, Show, Generic, Hashable)

relativeTo :: Position.Absolute -> Span.Absolute -> Span.Relative
relativeTo base (Span.Absolute start end) =
  Span.Relative (Position.relativeTo base start) (Position.relativeTo base end)

add :: Position.Absolute -> Span.Relative -> Span.Absolute
add base (Span.Relative start end) =
  Span.Absolute (Position.add base start) (Position.add base end)
