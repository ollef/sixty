{-# language FlexibleContexts #-}
module LanguageServer.LineColumn where

import Protolude hiding (moduleName)

import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified Name
import qualified Position
import Query (Query)
import qualified Query
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Span
import Span (LineColumn(LineColumns))

fromKeyedName :: MonadFetch Query m => Scope.KeyedName -> m (Span.Relative -> Span.LineColumn)
fromKeyedName keyedName = do
  (filePath, Span.Absolute absolutePosition _) <-
    fetch $ Query.KeyedNameSpan keyedName

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

  return $ toLineColumns . Span.absoluteFrom absolutePosition

fromAbsolute :: MonadFetch Query m => Name.Module -> m (Span.Absolute -> Span.LineColumn)
fromAbsolute moduleName = do
  maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query moduleName
  case maybeFilePath of
    Nothing ->
      pure $ const $ Span.LineColumns (Position.LineColumn 0 0) (Position.LineColumn 0 0)

    Just filePath -> do
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

      return toLineColumns
