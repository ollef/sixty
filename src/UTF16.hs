{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module UTF16 where

import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text
import qualified Data.Text.Utf16.Lines as Utf16.Lines
import qualified Position
import Prettyprinter (Pretty (pretty))
import Protolude hiding (length)
import qualified Span

newtype CodeUnits = CodeUnits {toInt :: Int}
  deriving (Eq, Ord, Show, Generic, NFData, Num)

length :: Text -> CodeUnits
length = CodeUnits . fromIntegral . Utf16.Lines.length . Utf16.Lines.fromText

data LineColumn = LineColumn !Int !CodeUnits
  deriving (Eq, Ord, Show, Generic)

data LineColumns = LineColumns !LineColumn !LineColumn
  deriving (Show, Generic)

lineColumn :: Position.Absolute -> Text -> (LineColumn, Text)
lineColumn (Position.Absolute index) text =
  let prefix = Text.takeWord8 index text
      suffix = Text.dropWord8 index text
      linePrefix = Text.takeWhileEnd (/= '\n') prefix
      linePrefixLength = Text.lengthWord8 linePrefix
      linePrefixLength16 = length linePrefix
      lineSuffixLength = Text.lengthWord8 $ Text.takeWhile (/= '\n') suffix
      lineStart = index - linePrefixLength
      lineLength = linePrefixLength + lineSuffixLength
      line = Text.takeWord8 lineLength $ Text.dropWord8 lineStart text
   in ( LineColumn
          (Text.count "\n" prefix)
          linePrefixLength16
      , line
      )

lineColumns :: Span.Absolute -> Text -> (LineColumns, Text)
lineColumns (Span.Absolute start end) text =
  let (startLineColumn, lineText) =
        lineColumn start text
   in ( LineColumns
          startLineColumn
          (fst $ lineColumn end text)
      , lineText
      )

-- | Gives a summary (fileName:row:column) of the location
instance Pretty LineColumns where
  pretty
    ( LineColumns
        start@(LineColumn ((+ 1) -> startLine) (CodeUnits ((+ 1) -> startColumn)))
        end@(LineColumn ((+ 1) -> endLine) (CodeUnits ((+ 1) -> endColumn)))
      )
      | start == end =
          pretty startLine <> ":" <> pretty startColumn
      | startLine == endLine =
          pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endColumn
      | otherwise =
          pretty startLine <> ":" <> pretty startColumn <> "-" <> pretty endLine <> ":" <> pretty endColumn
