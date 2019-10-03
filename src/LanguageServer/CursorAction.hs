{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module LanguageServer.CursorAction where

import Protolude hiding (IntMap, evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Rope.UTF16 as Rope
import Rock

import qualified Binding
import Binding (Binding)
import Context (Context)
import qualified Context
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Domain
import qualified Elaboration
import qualified Index
import Monad
import qualified Name
import Plicity
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
import qualified TypeOf
import qualified Var
import Var (Var)

type Callback a =
  forall v. Context v -> IntMap Var (Scope.KeyedName, Span.Relative) -> Syntax.Term v -> Span.LineColumn -> MaybeT M a

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

        k' env term actionSpan =
          k
            (_context env)
            ((,) (Scope.KeyedName key (Name.Qualified moduleName name)) <$>_varSpans env)
            term
            (toLineColumns $ Span.trim contents $ Span.absoluteFrom defPos actionSpan)
      context <- Context.empty $ Scope.KeyedName key qualifiedName
      definitionAction
        k'
        Environment
          { _actionPosition = Position.relativeTo defPos pos
          , _context = context
          , _varSpans = mempty
          }
        key
        qualifiedName
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

data Environment v = Environment
  { _actionPosition :: !Position.Relative
  , _context :: Context v
  , _varSpans :: IntMap Var Span.Relative
  }

extend :: Environment v -> Binding -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extend env binding type_ = do
  type' <- lift $ Elaboration.evaluate (_context env) type_
  (context', var) <- lift $ Context.extendUnnamed (_context env) (Binding.toName binding) type'
  pure
    ( env
      { _context = context'
      , _varSpans = maybe identity (IntMap.insert var) (Binding.span binding) (_varSpans env)
      }
    , var
    )

type RelativeCallback a =
  forall v. Environment v -> Syntax.Term v -> Span.Relative -> MaybeT M a

definitionAction
  :: forall a
  . RelativeCallback a
  -> Environment Void
  -> Scope.Key
  -> Name.Qualified
  -> MaybeT M a
definitionAction k env key qualifiedName =
  definitionNameActions <|>
  case key of
    Scope.Type -> do
      type_ <- fetch $ Query.ElaboratedType qualifiedName
      termAction k env type_

    Scope.Definition -> do
      maybeDef <- fetch $ Query.ElaboratedDefinition qualifiedName
      case maybeDef of
        Nothing ->
          empty

        Just (def, _) ->
          case def of
            Syntax.TypeDeclaration type_ ->
              termAction k env type_

            Syntax.ConstantDefinition term ->
              termAction k env term

            Syntax.DataDefinition tele ->
              dataDefinitionAction k env tele
  where
    definitionNameActions :: MaybeT M a
    definitionNameActions = do
      constructorSpans <- definitionConstructorSpans key qualifiedName
      spans <- definitionNameSpans key qualifiedName
      asum $
        (foreach constructorSpans $ \(span, constr) -> do
          guard $ span `Span.relativeContains` _actionPosition env
          k env (Syntax.Con constr) span
        ) <>
        (foreach spans $ \span -> do
          guard $ span `Span.relativeContains` _actionPosition env
          k env (Syntax.Global qualifiedName) span
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
  -> Environment v
  -> Syntax.Term v
  -> MaybeT M a
termAction k env term =
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
      (env', var) <- extend env binding type_
      bindingAction k env' binding var <|>
        termAction k env term' <|>
        termAction k env type_ <|>
        termAction k env' body

    Syntax.Pi binding source _ domain -> do
      (env', var) <- extend env binding source
      bindingAction k env' binding var <|>
        termAction k env source <|>
        termAction k env' domain

    Syntax.Fun source _ domain ->
      termAction k env source <|>
      termAction k env domain

    Syntax.Lam binding type_ _ body -> do
      (env', var) <- extend env binding type_
      bindingAction k env' binding var <|>
        termAction k env type_ <|>
        termAction k env' body

    Syntax.App t1 _ t2 ->
      termAction k env t1 <|>
      termAction k env t2

    Syntax.Case scrutinee branches defaultBranch ->
      termAction k env scrutinee <|>
      asum (branchAction k env scrutinee <$> HashMap.toList branches) <|>
      asum (termAction k env <$> defaultBranch)

    Syntax.Spanned span term' ->
      termAction k env term' <|> do
        guard $ span `Span.relativeContains` _actionPosition env
        k env term' span

dataDefinitionAction
  :: RelativeCallback a
  -> Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> MaybeT M a
dataDefinitionAction k env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      asum $ termAction k env <$> HashMap.elems constrDefs

    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extend env binding type_
      bindingAction k env' binding var <|>
        termAction k env type_ <|>
        dataDefinitionAction k env' tele'

branchAction
  :: RelativeCallback a
  -> Environment v
  -> Syntax.Term v
  -> (Name.QualifiedConstructor, (Span.Relative, Telescope Syntax.Type Syntax.Term v))
  -> MaybeT M a
branchAction k env scrutinee (constr@(Name.QualifiedConstructor typeName _), (span, tele)) =
  (do
    guard $ span `Span.relativeContains` _actionPosition env
    scrutinee' <- lift $ Elaboration.evaluate (_context env) scrutinee
    scrutineeType <- lift $ TypeOf.typeOf (_context env) scrutinee'
    scrutineeType' <- lift $ Context.forceHead (_context env) scrutineeType
    case scrutineeType' of
      Domain.Neutral (Domain.Global headName) spine
        | headName == typeName -> do
          spine' <- lift $ mapM (mapM $ Elaboration.readback $ _context env) spine
          k env (Syntax.Con constr `Syntax.apps` fmap (first implicitise) spine') span

      _ ->
        k env (Syntax.Con constr) span
  ) <|>
  teleAction k env tele

teleAction
  :: RelativeCallback a
  -> Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> MaybeT M a
teleAction k env tele =
  case tele of
    Telescope.Empty branch ->
      termAction k env branch

    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extend env binding type_
      bindingAction k env' binding var <|>
        termAction k env type_ <|>
        teleAction k env' tele'

bindingAction
  :: RelativeCallback a
  -> Environment (Index.Succ v)
  -> Binding
  -> Var
  -> MaybeT M a
bindingAction k env binding var =
  case binding of
    Binding.Spanned span _ -> do
      guard $ span `Span.relativeContains` _actionPosition env
      case Context.lookupVarIndex var $ _context env of
        Nothing ->
          empty

        Just index ->
          k env (Syntax.Var index) span

    Binding.Unspanned _ ->
      empty
