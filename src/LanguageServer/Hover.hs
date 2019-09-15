{-# language OverloadedStrings #-}
module LanguageServer.Hover where

import Protolude hiding (evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Data.Text.Prettyprint.Doc (Doc, (<+>))
import Rock

import Context (Context)
import qualified Context
import qualified Elaboration
import Monad
import qualified Error.Hydrated as Error
import qualified Name
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified TypeOf

hover :: FilePath -> Text -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath contents (Position.LineColumn line column) = do
  (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  results <- forM (HashMap.toList spans) $ \((key, name), span@(Span.Absolute defPos _)) ->
    if span `Span.contains` pos then do
      let
        qualifiedName =
          Name.Qualified moduleName name
      context <- Context.empty $ Scope.KeyedName key qualifiedName
      maybeResult <- hoverDefinition (Position.relativeTo defPos pos) context key qualifiedName
      pure $ first (toLineColumns . Span.absoluteFrom defPos) <$> maybeResult

    else
      pure Nothing

  pure $ listToMaybe $ catMaybes results
  where
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

hoverDefinition
  :: Position.Relative
  -> Context Void
  -> Scope.Key
  -> Name.Qualified
  -> Task Query (Maybe (Span.Relative, Doc ann))
hoverDefinition pos context key name = do
  result <-
    runM $
    runMaybeT $
      case key of
        Scope.Type -> do
          type_ <- fetch $ Query.ElaboratedType name
          hoverTerm pos context type_

        Scope.Definition -> do
          maybeDef <- fetch $ Query.ElaboratedDefinition name
          case maybeDef of
            Nothing ->
              empty

            Just (def, _) ->
              case def of
                Syntax.TypeDeclaration type_ ->
                  hoverTerm pos context type_

                Syntax.ConstantDefinition term ->
                  hoverTerm pos context term

                Syntax.DataDefinition tele ->
                  hoverDataDefinition pos context tele
  case result of
    Left _ ->
      pure Nothing

    Right res ->
      pure res

hoverTerm
  :: Position.Relative
  -> Context v
  -> Syntax.Term v
  -> MaybeT M (Span.Relative, Doc ann)
hoverTerm pos context term =
  case term of
    Syntax.Var _ ->
      empty

    Syntax.Global _ ->
      empty

    Syntax.Con _ ->
      empty

    Syntax.Meta _ ->
      empty

    Syntax.Let name term' type_ body -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', _) <- lift $ Context.extendUnnamed context name type'
      hoverTerm pos context term' <|>
        hoverTerm pos context type_ <|>
        hoverTerm pos context' body

    Syntax.Pi name source _ domain -> do
      source' <- lift $ Elaboration.evaluate context source
      (context', _) <- lift $ Context.extendUnnamed context name source'
      hoverTerm pos context source <|>
        hoverTerm pos context' domain

    Syntax.Fun source domain ->
      hoverTerm pos context source <|>
      hoverTerm pos context domain

    Syntax.Lam name type_ _ body -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', _) <- lift $ Context.extendUnnamed context name type'
      hoverTerm pos context type_ <|>
        hoverTerm pos context' body

    Syntax.App t1 _ t2 ->
      hoverTerm pos context t1 <|>
      hoverTerm pos context t2

    Syntax.Case scrutinee branches defaultBranch ->
      hoverTerm pos context scrutinee <|>
      asum (hoverBranch pos context <$> HashMap.elems branches) <|>
      asum (hoverTerm pos context <$> defaultBranch)

    Syntax.Spanned span term' ->
      hoverTerm pos context term' <|>
      if span `Span.relativeContains` pos then do
        term'' <- lift $ Elaboration.evaluate context term'
        type_ <- lift $ TypeOf.typeOf context term''
        type' <- lift $ Elaboration.readback context type_
        prettyTerm <- Error.prettyPrettyableTerm $ Context.toPrettyableTerm context term'
        prettyType <- Error.prettyPrettyableTerm $ Context.toPrettyableTerm context type'
        pure
          ( span
          , prettyTerm <+> ":" <+> prettyType
          )

      else
        empty

hoverDataDefinition
  :: Position.Relative
  -> Context v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> MaybeT M (Span.Relative, Doc ann)
hoverDataDefinition pos context tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      asum $ hoverTerm pos context <$> HashMap.elems constrDefs

    Telescope.Extend name type_ _ tele' -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', _) <- lift $ Context.extendUnnamed context name type'
      hoverTerm pos context type_ <|>
        hoverDataDefinition pos context' tele'

hoverBranch
  :: Position.Relative
  -> Context v
  -> Telescope Syntax.Type Syntax.Term v
  -> MaybeT M (Span.Relative, Doc ann)
hoverBranch pos context tele =
  case tele of
    Telescope.Empty branch ->
      hoverTerm pos context branch

    Telescope.Extend name type_ _ tele' -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', _) <- lift $ Context.extendUnnamed context name type'
      hoverTerm pos context type_ <|>
        hoverBranch pos context' tele'
