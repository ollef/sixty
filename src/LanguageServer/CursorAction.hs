{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module LanguageServer.CursorAction where

import Protolude hiding (evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified Binding
import Binding (Binding)
import Context (Context)
import qualified Context
import qualified Elaboration
import qualified Index
import Monad
import qualified Name
import qualified Position
import qualified Presyntax
import Query (Query)
import qualified Query
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)

type Callback a =
  forall v. Context v -> Syntax.Term v -> Span.LineColumn -> MaybeT M a

cursorAction
  :: FilePath
  -> Text
  -> Position.LineColumn
  -> Callback a
  -> Task Query (Maybe a)
cursorAction filePath contents (Position.LineColumn line column) k = do
  result <- runM $ runMaybeT $ do
    (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
    spans <- fetch $ Query.ModuleSpanMap moduleName

    asum $ foreach (HashMap.toList spans) $ \((key, name), span@(Span.Absolute defPos _)) -> do
      guard $ span `Span.contains` pos
      let
        qualifiedName =
          Name.Qualified moduleName name

        k' context term actionSpan =
          k context term (toLineColumns $ Span.absoluteFrom defPos actionSpan)
      context <- Context.empty $ Scope.KeyedName key qualifiedName
      definitionAction k' (Position.relativeTo defPos pos) context key qualifiedName
  pure $ case result of
    Left _ ->
      Nothing

    Right result' ->
      result'
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

type RelativeCallback a =
  forall v. Context v -> Syntax.Term v -> Span.Relative -> MaybeT M a

definitionAction
  :: forall a
  . RelativeCallback a
  -> Position.Relative
  -> Context Void
  -> Scope.Key
  -> Name.Qualified
  -> MaybeT M a
definitionAction k pos context key qualifiedName =
  definitionNameActions <|>
  case key of
    Scope.Type -> do
      type_ <- fetch $ Query.ElaboratedType qualifiedName
      termAction k pos context type_

    Scope.Definition -> do
      maybeDef <- fetch $ Query.ElaboratedDefinition qualifiedName
      case maybeDef of
        Nothing ->
          empty

        Just (def, _) ->
          case def of
            Syntax.TypeDeclaration type_ ->
              termAction k pos context type_

            Syntax.ConstantDefinition term ->
              termAction k pos context term

            Syntax.DataDefinition tele ->
              dataDefinitionAction k pos context tele
  where
    definitionNameActions :: MaybeT M a
    definitionNameActions = do
      constructorSpans <- definitionConstructorSpans key qualifiedName
      spans <- definitionNameSpans key qualifiedName
      asum $
        (foreach constructorSpans $ \(span, constr) -> do
          guard $ span `Span.relativeContains` pos
          k context (Syntax.Con constr) span
        ) <>
        (foreach spans $ \span -> do
          guard $ span `Span.relativeContains` pos
          k context (Syntax.Global qualifiedName) span
        )

definitionNameSpans :: MonadFetch Query m => Scope.Key -> Name.Qualified -> m [Span.Relative]
definitionNameSpans key (Name.Qualified moduleName name) = do
  maybeParsedDefinition <- fetch $ Query.ParsedDefinition moduleName $ Mapped.Query (key, name)
  pure $
    case maybeParsedDefinition of
      Nothing ->
        []

      Just parsedDefinition ->
        Presyntax.spans parsedDefinition

definitionConstructorSpans
  :: MonadFetch Query m
  => Scope.Key
  -> Name.Qualified
  -> m [(Span.Relative, Name.QualifiedConstructor)]
definitionConstructorSpans key qualifiedName@(Name.Qualified moduleName name) = do
  maybeParsedDefinition <- fetch $ Query.ParsedDefinition moduleName $ Mapped.Query (key, name)
  pure $
    case maybeParsedDefinition of
      Nothing ->
        []

      Just parsedDefinition ->
        second (Name.QualifiedConstructor qualifiedName) <$> Presyntax.constructorSpans parsedDefinition

termAction
  :: RelativeCallback a
  -> Position.Relative
  -> Context v
  -> Syntax.Term v
  -> MaybeT M a
termAction k pos context term =
  case term of
    Syntax.Var _ ->
      empty

    Syntax.Global _ ->
      empty

    Syntax.Con _ ->
      empty

    Syntax.Meta _ ->
      empty

    Syntax.Let binding term' type_ body -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) type'
      bindingAction k pos context' binding var <|>
        termAction k pos context term' <|>
        termAction k pos context type_ <|>
        termAction k pos context' body

    Syntax.Pi binding source _ domain -> do
      source' <- lift $ Elaboration.evaluate context source
      (context', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) source'
      bindingAction k pos context' binding var <|>
        termAction k pos context source <|>
        termAction k pos context' domain

    Syntax.Fun source domain ->
      termAction k pos context source <|>
      termAction k pos context domain

    Syntax.Lam binding type_ _ body -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) type'
      bindingAction k pos context' binding var <|>
        termAction k pos context type_ <|>
        termAction k pos context' body

    Syntax.App t1 _ t2 ->
      termAction k pos context t1 <|>
      termAction k pos context t2

    Syntax.Case scrutinee branches defaultBranch ->
      termAction k pos context scrutinee <|>
      asum (branchAction k pos context <$> HashMap.elems branches) <|>
      asum (termAction k pos context <$> defaultBranch)

    Syntax.Spanned span term' ->
      termAction k pos context term' <|> do
        guard $ span `Span.relativeContains` pos
        k context term' span

dataDefinitionAction
  :: RelativeCallback a
  -> Position.Relative
  -> Context v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> MaybeT M a
dataDefinitionAction k pos context tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      asum $ termAction k pos context <$> HashMap.elems constrDefs

    Telescope.Extend binding type_ _ tele' -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) type'
      bindingAction k pos context' binding var <|>
        termAction k pos context type_ <|>
        dataDefinitionAction k pos context' tele'

branchAction
  :: RelativeCallback a
  -> Position.Relative
  -> Context v
  -> Telescope Syntax.Type Syntax.Term v
  -> MaybeT M a
branchAction k pos context tele =
  case tele of
    Telescope.Empty branch ->
      termAction k pos context branch

    Telescope.Extend binding type_ _ tele' -> do
      type' <- lift $ Elaboration.evaluate context type_
      (context', var) <- lift $ Context.extendUnnamed context (Binding.toName binding) type'
      bindingAction k pos context' binding var <|>
        termAction k pos context type_ <|>
        branchAction k pos context' tele'

bindingAction
  :: RelativeCallback a
  -> Position.Relative
  -> Context (Index.Succ v)
  -> Binding
  -> Var
  -> MaybeT M a
bindingAction k pos context binding var =
  case binding of
    Binding.Spanned span _ -> do
      guard $ span `Span.relativeContains` pos
      case Context.lookupVarIndex var context of
        Nothing ->
          empty

        Just index ->
          k context (Syntax.Var index) span

    Binding.Unspanned _ ->
      empty
