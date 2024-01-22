{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Position where

import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text
import Protolude

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, NFData)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show, Generic, NFData)

addLine :: LineColumn -> LineColumn
addLine (LineColumn line _) =
  LineColumn (line + 1) 0

addColumns :: LineColumn -> Int -> LineColumn
addColumns (LineColumn line column) delta =
  LineColumn line $ column + delta

lineColumn :: Absolute -> Text -> (LineColumn, Text)
lineColumn (Absolute index) text =
  let prefix =
        Text.takeWord8 index text

      suffix =
        Text.dropWord8 index text

      linePrefixLength =
        Text.lengthWord8 $ Text.takeWhileEnd (/= '\n') prefix

      lineSuffixLength =
        Text.lengthWord8 $ Text.takeWhile (/= '\n') suffix

      lineStart =
        index - linePrefixLength

      lineLength =
        linePrefixLength + lineSuffixLength

      line =
        Text.takeWord8 lineLength $
          Text.dropWord8 lineStart text
   in ( LineColumn
          (Text.count "\n" prefix)
          linePrefixLength
      , line
      )
