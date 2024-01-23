{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}

module LanguageServer.DocumentHighlights where

import Data.HashMap.Lazy as HashMap
import qualified Data.Text.Utf16.Rope as Rope
import qualified LanguageServer.LineColumns as LineColumns
import qualified Name
import qualified Occurrences.Intervals as Intervals
import qualified Position
import Protolude hiding (moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Span
import qualified UTF16

highlights
  :: FilePath
  -> UTF16.LineColumn
  -> Task Query [UTF16.LineColumns]
highlights filePath (UTF16.LineColumn line column) = do
  (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  contents <- fetch $ Query.FileRope filePath
  let pos =
        Position.Absolute $
          case Rope.splitAtPosition (Rope.Position (fromIntegral line) (fromIntegral $ UTF16.toInt column)) contents of
            Nothing -> 0
            Just (rope, _) -> fromIntegral $ Rope.utf8Length rope

  toLineColumns <- LineColumns.fromAbsolute moduleName

  let itemSpans item =
        fmap concat $
          forM (HashMap.toList spans) \((definitionKind, name), Span.Absolute defPos _) -> do
            occurrenceIntervals <-
              fetch $
                Query.Occurrences definitionKind $
                  Name.Qualified moduleName name
            pure $ toLineColumns . Span.absoluteFrom defPos <$> Intervals.itemSpans item occurrenceIntervals

  fmap concat $
    forM (HashMap.toList spans) \((definitionKind, name), span@(Span.Absolute defPos _)) ->
      if span `Span.contains` pos
        then do
          occurrenceIntervals <-
            fetch $
              Query.Occurrences definitionKind $
                Name.Qualified moduleName name
          let relativePos =
                Position.relativeTo defPos pos

              items =
                Intervals.intersect relativePos occurrenceIntervals

          fmap concat $
            forM items \item ->
              case item of
                Intervals.Var var ->
                  pure $ toLineColumns . Span.absoluteFrom defPos <$> Intervals.varSpans var relativePos occurrenceIntervals
                Intervals.Global _ ->
                  itemSpans item
                Intervals.Con _ ->
                  itemSpans item
                Intervals.Lit _ ->
                  itemSpans item
        else pure []
