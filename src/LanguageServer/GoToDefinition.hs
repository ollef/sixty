{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.GoToDefinition where

import Protolude hiding (IntMap, evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Rope.UTF16 as Rope
import qualified Data.Text.IO as Text
import Rock

import Context (Context)
import qualified Context
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified LanguageServer.CursorAction as CursorAction
import Monad
import qualified Name
import qualified Occurrences
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import Span (LineColumn(LineColumns))
import qualified Span
import qualified Syntax
import Var (Var)
import qualified Var

goToDefinition :: FilePath -> Position.LineColumn -> Task Query (Maybe (FilePath, Span.LineColumn))
goToDefinition filePath pos = do
  CursorAction.cursorAction filePath pos $ \item _ ->
    case item of
      CursorAction.Import moduleName -> do
        moduleFile <- Query.fetchModuleFile moduleName
        pure (moduleFile, Span.LineColumns (Position.LineColumn 0 0) (Position.LineColumn 0 0))

      CursorAction.Term _ context varSpans term -> do
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
        (keyedName, relativeSpans) <- go context varSpans term
        (file, Span.Absolute absolutePosition _) <- fetch $ Query.KeyedNameSpan keyedName
        let
          absoluteSpans =
            toLineColumns . Span.absoluteFrom absolutePosition <$> relativeSpans

          spanStart (LineColumns s _) =
            s

          resultSpan
            | filePath == file =
              case sortBy (flip $ comparing spanStart) $ NonEmpty.filter ((<= pos) . spanStart) absoluteSpans of
                span:_ ->
                  span

                [] ->
                  NonEmpty.head absoluteSpans
            | otherwise =
              NonEmpty.head absoluteSpans

        liftIO $ Text.hPutStrLn stderr $ show absoluteSpans

        pure (file, resultSpan)

go
  :: Context v
  -> IntMap Var (NonEmpty Span.Relative)
  -> Syntax.Term v
  -> MaybeT M (Scope.KeyedName, NonEmpty Span.Relative)
go context varMap term =
  case term of
    Syntax.Var index ->
      asum $ pure . (,) (Context.scopeKey context) <$> IntMap.lookup (Context.lookupIndexVar index context) varMap

    Syntax.Global qualifiedName -> do
      asum $ foreach [Scope.Type, Scope.Definition] $ \key -> do
        spans <- Occurrences.definitionNameSpans key qualifiedName
        asum $ pure <$> ((,) (Scope.KeyedName key qualifiedName) . pure <$> spans)

    Syntax.Con constr@(Name.QualifiedConstructor qualifiedName _) -> do
      spans <- Occurrences.definitionConstructorSpans Scope.Definition qualifiedName
      asum $ pure <$>
        mapMaybe
          (\(span, constr') ->
            if constr == constr' then
              Just (Scope.KeyedName Scope.Definition qualifiedName, pure span)
            else
              Nothing
          )
          spans

    Syntax.Meta _ ->
      empty

    Syntax.Let {} ->
      empty

    Syntax.Pi {} ->
      empty

    Syntax.Fun {} ->
      empty

    Syntax.Lam {} ->
      empty

    Syntax.App term' _ _ ->
      go context varMap term'

    Syntax.Case {} ->
      empty

    Syntax.Spanned _ term' ->
      go context varMap term'
