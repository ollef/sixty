module LanguageServer.DocumentHighlights where

import Protolude hiding (moduleName)

import Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Rock

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
    rope =
      Rope.fromText contents

    toLineColumn (Position.Absolute i) =
      let
        rope' =
          Rope.take i rope
      in
      Position.LineColumn (Rope.rows rope') (Rope.columns rope')

    toLineColumns (Span.Absolute start end) =
      Span.LineColumns (toLineColumn start) (toLineColumn end)

    pos =
      Position.Absolute $ Rope.rowColumnCodeUnits (Rope.RowColumn line column) rope
  fmap concat $ forM (HashMap.toList spans) $ \((key, name), span@(Span.Absolute defPos _)) ->
    if span `Span.contains` pos then do
      occurrenceIntervals <- fetch $
        Query.Occurrences $
        Scope.KeyedName key $
        Name.Qualified moduleName name
      let
        relativePos =
          Position.relativeTo defPos pos

        relativeIntervals =
          Intervals.intersect relativePos occurrenceIntervals
      pure $
        toLineColumns . Span.absoluteFrom defPos <$> relativeIntervals

    else
      pure []
