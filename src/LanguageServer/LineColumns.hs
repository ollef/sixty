{-# LANGUAGE FlexibleContexts #-}

module LanguageServer.LineColumns where

import qualified Data.Rope.UTF16 as Rope
import qualified Name
import qualified Position
import Protolude hiding (moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import Span (LineColumn (LineColumns))
import qualified Span

fromDefinitionName :: MonadFetch Query m => Scope.DefinitionKind -> Name.Qualified -> m (Span.Relative -> Span.LineColumn)
fromDefinitionName definitionKind name@(Name.Qualified moduleName _) = do
  (_, absolutePosition) <- fetch $ Query.DefinitionPosition definitionKind name
  toLineColumns <- fromAbsolute moduleName
  pure $ toLineColumns . Span.absoluteFrom absolutePosition

fromAbsolute :: MonadFetch Query m => Name.Module -> m (Span.Absolute -> Span.LineColumn)
fromAbsolute moduleName = do
  maybeFilePath <- fetch $ Query.ModuleFile moduleName
  case maybeFilePath of
    Nothing ->
      pure $ const $ Span.LineColumns (Position.LineColumn 0 0) (Position.LineColumn 0 0)
    Just filePath -> do
      contents <- fetch $ Query.FileText filePath
      let -- TODO use the rope that we get from the LSP library instead
          rope =
            Rope.fromText contents

          toLineColumn (Position.Absolute i) =
            let rope' =
                  Rope.take i rope
             in Position.LineColumn (Rope.rows rope') (Rope.columns rope')

          toLineColumns (Span.Absolute start end) =
            Span.LineColumns (toLineColumn start) (toLineColumn end)

      return toLineColumns
