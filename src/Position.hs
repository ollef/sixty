{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Position where

import Protolude

import Data.Persist

import qualified Data.ByteString as ByteString

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, Persist, NFData)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, Persist)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show, Generic, Persist, NFData)

addLine :: LineColumn -> LineColumn
addLine (LineColumn line _) =
  LineColumn (line + 1) 0

addColumns :: LineColumn -> Int -> LineColumn
addColumns (LineColumn line column) delta =
  LineColumn line $ column + delta

lineColumn :: Absolute -> ByteString -> (LineColumn, ByteString)
lineColumn (Absolute index) text =
  let
    (prefix, suffix) =
      ByteString.splitAt index text

    linePrefixLength =
      ByteString.length $ ByteString.takeWhileEnd (/= fromIntegral (ord '\n')) prefix

    lineSuffixLength =
      ByteString.length $ ByteString.takeWhile (/= fromIntegral (ord '\n')) suffix

    lineStart =
      index - linePrefixLength

    lineLength =
      linePrefixLength + lineSuffixLength

    line =
      ByteString.take lineLength $
      ByteString.drop lineStart text
  in
  ( LineColumn
    (ByteString.count (fromIntegral $ ord '\n') prefix)
    linePrefixLength
  , line
  )
