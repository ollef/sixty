{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.GoToDefinition where

import Protolude hiding (IntMap, evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.Rope.UTF16 as Rope
import Rock

import Context (Context)
import qualified Context
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified LanguageServer.CursorAction as CursorAction
import Monad
import qualified Name
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span
import qualified Syntax
import Var (Var)
import qualified Var

goToDefinition :: FilePath -> Position.LineColumn -> Task Query (Maybe (FilePath, Span.LineColumn))
goToDefinition filePath pos = do
  CursorAction.cursorAction filePath pos $ \context varSpans term _ -> do
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
    (keyedName, relativeSpan) <- go context varSpans term
    (file, Span.Absolute absolutePosition _) <- fetch $ Query.KeyedNameSpan keyedName
    pure (file, toLineColumns $ Span.absoluteFrom absolutePosition relativeSpan)

go
  :: Context v
  -> IntMap Var (Scope.KeyedName, Span.Relative)
  -> Syntax.Term v
  -> MaybeT M (Scope.KeyedName, Span.Relative)
go context varMap term =
  case term of
    Syntax.Var index ->
      asum $ pure <$> IntMap.lookup (Context.lookupIndexVar index context) varMap

    Syntax.Global qualifiedName -> do
      asum $ foreach [Scope.Type, Scope.Definition] $ \key -> do
        spans <- CursorAction.definitionNameSpans key qualifiedName
        asum $ pure <$> ((,) (Scope.KeyedName key qualifiedName) <$> spans)

    Syntax.Con constr@(Name.QualifiedConstructor qualifiedName _) -> do
      spans <- CursorAction.definitionConstructorSpans Scope.Definition qualifiedName
      asum $ pure <$>
        mapMaybe
          (\(span, constr') ->
            if constr == constr' then
              Just (Scope.KeyedName Scope.Definition qualifiedName, span)
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
