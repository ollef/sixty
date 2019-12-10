{-# LANGUAGE FlexibleContexts #-}
module LanguageServer.DocumentHighlights where

import Protolude hiding (moduleName)

import Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified LanguageServer.LineColumns as LineColumns
import qualified Name
import qualified Occurrences.Intervals as Intervals
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

highlights
  :: FilePath
  -> Position.LineColumn
  -> Task Query [Span.LineColumn]
highlights filePath (Position.LineColumn line column) = do
  (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  contents <- fetch $ Query.FileText filePath
  let
    -- TODO use the rope that we get from the LSP library instead
    pos =
      Position.Absolute $
        Rope.rowColumnCodeUnits (Rope.RowColumn line column) $
        Rope.fromText contents

  toLineColumns <- LineColumns.fromAbsolute moduleName

  let
    itemSpans item =
      fmap concat $ forM (HashMap.toList spans) $ \((key, name), (Span.Absolute defPos _)) -> do
        occurrenceIntervals <- fetch $
          Query.Occurrences $
          Scope.KeyedName key $
          Name.Qualified moduleName name
        pure $ toLineColumns . Span.absoluteFrom defPos <$> Intervals.itemSpans item occurrenceIntervals

  fmap concat $ forM (HashMap.toList spans) $ \((key, name), span@(Span.Absolute defPos _)) ->
    if span `Span.contains` pos then do
      occurrenceIntervals <- fetch $
        Query.Occurrences $
        Scope.KeyedName key $
        Name.Qualified moduleName name
      let
        relativePos =
          Position.relativeTo defPos pos

        items =
          Intervals.intersect relativePos occurrenceIntervals

      fmap concat $ forM items $ \item ->
        case item of
          Intervals.Var var ->
            pure $ toLineColumns . Span.absoluteFrom defPos <$> Intervals.varSpans var relativePos occurrenceIntervals

          Intervals.Global _ ->
            itemSpans item

          Intervals.Con _ ->
            itemSpans item

    else
      pure []
