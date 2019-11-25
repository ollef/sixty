{-# language FlexibleContexts #-}
module LanguageServer.LineColumn where

import Protolude hiding (moduleName)

import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified Position
import Query (Query)
import qualified Query
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
