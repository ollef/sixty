{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
{-# language ViewPatterns #-}
module Span where

import Protolude

import qualified Data.Char as Char
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import qualified Data.Text.Unsafe as Text

import qualified Position

data Absolute = Absolute !Position.Absolute !Position.Absolute
  deriving (Eq, Ord, Show, Generic, Hashable)

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
  deriving Show

lineColumn :: Absolute -> Text -> (LineColumn, Text)
lineColumn (Absolute start end) text =
  let
    (startLineColumn, lineText) =
      Position.lineColumn start text
  in
  ( LineColumns
    startLineColumn
    (fst $ Position.lineColumn end text)
  , lineText
  )

-- | Gives a summary (fileName:row:column) of the location
instance Pretty LineColumn where
  pretty
    (LineColumns
      start@(Position.LineColumn ((+ 1) -> startLine) ((+ 1) -> startColumn))
      end@(Position.LineColumn ((+ 1) -> endLine) ((+ 1) -> endColumn)))
    | start == end =
      pretty startLine <> ":" <> pretty startColumn

    | startLine == endLine =
      pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endColumn

    | otherwise =
      pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endLine <> ":" <> pretty endColumn

trim
  :: Text
  -> Span.Absolute
  -> Span.Absolute
trim text (Absolute (Position.Absolute start) (Position.Absolute end)) =
  let
    span =
      Text.takeWord16 (end - start) $
      Text.dropWord16 start text
    startSpaces =
      Text.lengthWord16 $
      Text.takeWhile Char.isSpace span
    endSpaces =
      Text.lengthWord16 $
      Text.takeWhileEnd Char.isSpace span
  in
  Absolute
    (Position.Absolute $ start + startSpaces)
    (Position.Absolute $ end - endSpaces)
