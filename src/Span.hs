{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Span where

import qualified Position
import Protolude

data Absolute = Absolute !Position.Absolute !Position.Absolute
  deriving (Eq, Ord, Show, Generic, Hashable, NFData)

data Relative = Relative !Position.Relative !Position.Relative
  deriving (Eq, Ord, Show, Generic, Hashable)

relativeTo :: Position.Absolute -> Span.Absolute -> Span.Relative
relativeTo base (Span.Absolute start end) =
  Span.Relative (Position.relativeTo base start) (Position.relativeTo base end)

absoluteFrom :: Position.Absolute -> Span.Relative -> Span.Absolute
absoluteFrom base (Span.Relative start end) =
  Span.Absolute (Position.add base start) (Position.add base end)

add :: Relative -> Relative -> Relative
add (Span.Relative start _) (Span.Relative _ end) =
  Span.Relative start end

contains :: Absolute -> Position.Absolute -> Bool
contains (Absolute start end) pos =
  start <= pos && pos < end

relativeContains :: Relative -> Position.Relative -> Bool
relativeContains (Relative start end) pos =
  start <= pos && pos < end

data LineColumn = LineColumns !Position.LineColumn !Position.LineColumn
  deriving (Show, Generic)
