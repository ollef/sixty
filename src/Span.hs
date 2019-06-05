{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Span where

import Protolude

import Data.Text.Prettyprint.Doc

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

data LineColumn = LineColumns !Position.LineColumn !Position.LineColumn
  deriving Show

lineColumn :: Absolute -> Text -> LineColumn
lineColumn (Absolute start end) text =
  LineColumns
    (Position.lineColumn start text)
    (Position.lineColumn end text)

-- | Gives a summary (fileName:row:column) of the location
instance Pretty LineColumn where
  pretty
    (LineColumns
      start@(Position.LineColumn startLine startColumn)
      end@(Position.LineColumn endLine endColumn))
    | start == end =
      pretty startLine <> ":" <> pretty startColumn

    | startLine == endLine =
      pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endColumn

    | otherwise =
      pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endLine <> ":" <> pretty endColumn
