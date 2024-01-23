{-# LANGUAGE FlexibleContexts #-}

module LanguageServer.LineColumns where

import qualified Data.Text.Utf16.Rope as Rope
import qualified Name
import qualified Position
import Protolude hiding (moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import qualified Span
import UTF16

fromDefinitionName :: (MonadFetch Query m) => Scope.DefinitionKind -> Name.Qualified -> m (Maybe (Span.Relative -> UTF16.LineColumns))
fromDefinitionName definitionKind name@(Name.Qualified moduleName _) = do
  (_, maybeAbsolutePosition) <- fetch $ Query.DefinitionPosition definitionKind name
  toLineColumns <- fromAbsolute moduleName
  pure $ fmap ((toLineColumns .) . Span.absoluteFrom) maybeAbsolutePosition

fromAbsolute :: (MonadFetch Query m) => Name.Module -> m (Span.Absolute -> UTF16.LineColumns)
fromAbsolute moduleName = do
  maybeFilePath <- fetch $ Query.ModuleFile moduleName
  case maybeFilePath of
    Nothing ->
      pure $ const $ UTF16.LineColumns (UTF16.LineColumn 0 0) (UTF16.LineColumn 0 0)
    Just filePath -> do
      rope <- fetch $ Query.FileRope filePath
      let toLineColumn (Position.Absolute i) =
            case Rope.utf8SplitAt (fromIntegral i) rope of
              Nothing -> UTF16.LineColumn 0 0
              Just (rope', _) ->
                let Rope.Position row column = Rope.lengthAsPosition rope'
                 in UTF16.LineColumn (fromIntegral row) (fromIntegral column)

          toLineColumns (Span.Absolute start end) =
            UTF16.LineColumns (toLineColumn start) (toLineColumn end)

      return toLineColumns
