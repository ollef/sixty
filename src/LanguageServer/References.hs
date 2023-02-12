{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}

module LanguageServer.References where

import qualified Builtin
import Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Text.Utf16.Rope as Rope
import qualified LanguageServer.LineColumns as LineColumns
import qualified Module
import qualified Name
import qualified Occurrences.Intervals as Intervals
import qualified Position
import Protolude hiding (moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Span

references
  :: FilePath
  -> Position.LineColumn
  -> Task Query [(Intervals.Item, [(FilePath, Span.LineColumn)])]
references filePath (Position.LineColumn line column) = do
  (originalModuleName, _, _) <- fetch $ Query.ParsedFile filePath
  let itemSpans definingModule item = do
        let mightUseDefiningModule moduleName header =
              moduleName == definingModule
                || any ((==) definingModule . (.module_)) header.imports
        inputFiles <- fetch Query.InputFiles
        fmap concat $
          forM (HashSet.toList inputFiles) \inputFile -> do
            (moduleName, header, _) <- fetch $ Query.ParsedFile inputFile
            if mightUseDefiningModule moduleName header
              then do
                spans <- fetch $ Query.ModuleSpanMap moduleName
                toLineColumns <- LineColumns.fromAbsolute moduleName
                fmap concat $
                  forM (HashMap.toList spans) \((definitionKind, name), Span.Absolute defPos _) -> do
                    occurrenceIntervals <-
                      fetch $
                        Query.Occurrences definitionKind $
                          Name.Qualified moduleName name
                    pure $ (,) inputFile . toLineColumns . Span.absoluteFrom defPos <$> Intervals.itemSpans item occurrenceIntervals
              else pure mempty

  contents <- fetch $ Query.FileText filePath
  let
    -- TODO use the rope that we get from the LSP library instead
    pos =
      Position.Absolute $
        case Rope.splitAtPosition (Rope.Position (fromIntegral line) (fromIntegral column)) $ Rope.fromText contents of
          Nothing -> 0
          Just (rope, _) -> fromIntegral $ Rope.length rope
  toLineColumns <- LineColumns.fromAbsolute originalModuleName
  spans <- fetch $ Query.ModuleSpanMap originalModuleName
  fmap concat $
    forM (HashMap.toList spans) \((definitionKind, name), span@(Span.Absolute defPos _)) ->
      if span `Span.contains` pos
        then do
          occurrenceIntervals <-
            fetch $
              Query.Occurrences definitionKind $
                Name.Qualified originalModuleName name
          let relativePos =
                Position.relativeTo defPos pos

              items =
                Intervals.intersect relativePos occurrenceIntervals

          forM items \item ->
            (,) item
              <$> case item of
                Intervals.Var var ->
                  pure $ (,) filePath . toLineColumns . Span.absoluteFrom defPos <$> Intervals.varSpans var relativePos occurrenceIntervals
                Intervals.Global (Name.Qualified definingModule _) ->
                  itemSpans definingModule item
                Intervals.Con (Name.QualifiedConstructor (Name.Qualified definingModule _) _) ->
                  itemSpans definingModule item
                Intervals.Lit _ ->
                  itemSpans Builtin.Module item
        else pure []
