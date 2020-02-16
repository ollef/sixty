{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
module LanguageServer.GoToDefinition where

import Protolude hiding (IntMap, evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified LanguageServer.LineColumns as LineColumns
import qualified Module
import qualified Name
import qualified Occurrences
import qualified Occurrences.Intervals as Intervals
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

goToDefinition :: FilePath -> Position.LineColumn -> Task Query (Maybe (FilePath, Span.LineColumn))
goToDefinition filePath (Position.LineColumn line column) = do
  (moduleName, moduleHeader, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  contents <- fetch $ Query.FileText filePath
  let
    -- TODO use the rope that we get from the LSP library instead
    pos =
      Position.Absolute $
        Rope.rowColumnCodeUnits (Rope.RowColumn line column) $
        Rope.fromText contents

  runMaybeT $ asum $
    foreach (Module._imports moduleHeader) (\import_ -> do
      let
        span =
          Module._span import_
      guard $ span `Span.contains` pos
      maybeDefiningFile <- fetch $ Query.ModuleFile $ Module._module import_
      case maybeDefiningFile of
        Nothing ->
          empty

        Just definingFile ->
          pure (definingFile, Span.LineColumns (Position.LineColumn 0 0) (Position.LineColumn 0 0))
    )
    <>
    foreach (HashMap.toList spans) (\((key, name), span@(Span.Absolute defPos _)) -> do
      guard $ span `Span.contains` pos
      occurrenceIntervals <- lift $ fetch $
        Query.Occurrences $
        Scope.KeyedName key $
        Name.Qualified moduleName name
      let
        relativePos =
          Position.relativeTo defPos pos

        items =
          Intervals.intersect relativePos occurrenceIntervals

      asum $ foreach items $ \case
        Intervals.Var var -> do
          toLineColumns <- LineColumns.fromKeyedName $ Scope.KeyedName key $ Name.Qualified moduleName name
          MaybeT $ pure $ (,) filePath . toLineColumns <$> Intervals.bindingSpan var relativePos occurrenceIntervals

        Intervals.Global qualifiedName@(Name.Qualified definingModule _)  ->
          asum $ foreach [Scope.Type, Scope.Definition] $ \definingKey -> do
            relativeSpans <- Occurrences.definitionNameSpans definingKey qualifiedName

            maybeDefiningFile <- fetch $ Query.ModuleFile definingModule
            case maybeDefiningFile of
              Nothing ->
                empty

              Just definingFile -> do
                toLineColumns <- LineColumns.fromKeyedName $ Scope.KeyedName definingKey qualifiedName
                asum $ pure . (,) definingFile . toLineColumns <$> relativeSpans

        Intervals.Con constr@(Name.QualifiedConstructor qualifiedName@(Name.Qualified definingModule _) _) -> do
          relativeSpans <- Occurrences.definitionConstructorSpans Scope.Definition qualifiedName
          maybeDefiningFile <- fetch $ Query.ModuleFile definingModule
          case maybeDefiningFile of
            Nothing ->
              empty

            Just definingFile -> do
              toLineColumns <- LineColumns.fromKeyedName $ Scope.KeyedName key qualifiedName
              asum $ pure <$>
                mapMaybe
                  (\(constrSpan, constr') ->
                    if constr == constr' then
                      Just (definingFile, toLineColumns constrSpan)
                    else
                      Nothing
                  )
                  relativeSpans
        Intervals.Lit _ ->
          empty
    )
