{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module LanguageServer.GoToDefinition where

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Text.Utf16.Rope as Rope
import qualified LanguageServer.LineColumns as LineColumns
import qualified Module
import qualified Name
import qualified Occurrences
import qualified Occurrences.Intervals as Intervals
import qualified Position
import Protolude hiding (IntMap, evaluate, moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import qualified Span

goToDefinition :: FilePath -> Position.LineColumn -> Task Query (Maybe (FilePath, Span.LineColumn))
goToDefinition filePath (Position.LineColumn line column) = do
  (moduleName, moduleHeader, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  rope <- fetch $ Query.FileRope filePath
  let pos =
        Position.Absolute $
          case Rope.splitAtPosition (Rope.Position (fromIntegral line) (fromIntegral column)) rope of
            Nothing -> 0
            Just (rope', _) -> fromIntegral $ Rope.length rope'

  runMaybeT $
    asum $
      foreach
        moduleHeader.imports
        ( \import_ -> do
            let span = import_.span
            guard $ span `Span.contains` pos
            maybeDefiningFile <- fetch $ Query.ModuleFile import_.module_
            case maybeDefiningFile of
              Nothing ->
                empty
              Just definingFile ->
                pure (definingFile, Span.LineColumns (Position.LineColumn 0 0) (Position.LineColumn 0 0))
        )
        <> foreach
          (HashMap.toList spans)
          ( \((definitionKind, name), span@(Span.Absolute defPos _)) -> do
              guard $ span `Span.contains` pos
              occurrenceIntervals <-
                lift $
                  fetch $
                    Query.Occurrences definitionKind $
                      Name.Qualified moduleName name
              let relativePos =
                    Position.relativeTo defPos pos

                  items =
                    Intervals.intersect relativePos occurrenceIntervals

              asum $
                foreach items $ \case
                  Intervals.Var var -> do
                    toLineColumns <- MaybeT $ LineColumns.fromDefinitionName definitionKind $ Name.Qualified moduleName name
                    MaybeT $
                      pure $
                        (,) filePath . toLineColumns <$> Intervals.bindingSpan var relativePos occurrenceIntervals
                  Intervals.Global qualifiedName@(Name.Qualified definingModule _) ->
                    asum $
                      foreach [Scope.Type, Scope.Definition] $ \definingKey -> do
                        relativeSpans <- Occurrences.definitionNameSpans definingKey qualifiedName

                        maybeDefiningFile <- fetch $ Query.ModuleFile definingModule
                        case maybeDefiningFile of
                          Nothing ->
                            empty
                          Just definingFile -> do
                            toLineColumns <- MaybeT $ LineColumns.fromDefinitionName definingKey qualifiedName
                            asum $ pure . (,) definingFile . toLineColumns <$> relativeSpans
                  Intervals.Con constr@(Name.QualifiedConstructor qualifiedName@(Name.Qualified definingModule _) _) -> do
                    relativeSpans <- Occurrences.definitionConstructorSpans Scope.Definition qualifiedName
                    maybeDefiningFile <- fetch $ Query.ModuleFile definingModule
                    case maybeDefiningFile of
                      Nothing ->
                        empty
                      Just definingFile -> do
                        toLineColumns <- MaybeT $ LineColumns.fromDefinitionName definitionKind qualifiedName
                        asum $
                          pure
                            <$> mapMaybe
                              ( \(constrSpan, constr') ->
                                  if constr == constr'
                                    then Just (definingFile, toLineColumns constrSpan)
                                    else Nothing
                              )
                              relativeSpans
                  Intervals.Lit _ ->
                    empty
          )
