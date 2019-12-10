{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module LanguageServer.CursorAction where

import Protolude hiding (IntMap, evaluate, moduleName)

import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import qualified Data.List.NonEmpty as NonEmpty
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
import qualified Module
import Monad
import qualified Name
import qualified Occurrences
import Plicity
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified TypeOf
import qualified Var
import Var (Var)
import qualified LanguageServer.LineColumns as LineColumns

type Callback a = ItemUnderCursor -> Span.LineColumn -> MaybeT M a

data ItemUnderCursor where
  Term
    :: ItemContext
    -> Context v
    -> IntMap Var (NonEmpty Span.Relative)
    -> Syntax.Term v
    -> ItemUnderCursor
  Import
    :: Name.Module
    -> ItemUnderCursor

data ItemContext
  = ExpressionContext
  | PatternContext
  | DefinitionContext
  deriving Show

cursorAction
  :: forall a
  . FilePath
  -> Position.LineColumn
  -> Callback a
  -> Task Query (Maybe a)
cursorAction filePath (Position.LineColumn line column) k = do
  result <- runM $ runMaybeT $ do
    (moduleName, moduleHeader, _) <- fetch $ Query.ParsedFile filePath
    spans <- fetch $ Query.ModuleSpanMap moduleName
    contents <- fetch $ Query.FileText filePath
    let
      -- TODO use the rope that we get from the LSP library instead
      pos =
        Position.Absolute $
          Rope.rowColumnCodeUnits (Rope.RowColumn line column) $
          Rope.fromText contents

    toLineColumns <- LineColumns.fromAbsolute moduleName
    asum $
      foreach (HashMap.toList spans) (\((key, name), span@(Span.Absolute defPos _)) -> do
        guard $ span `Span.contains` pos
        let
          qualifiedName =
            Name.Qualified moduleName name

          k' :: RelativeCallback a
          k' itemContext env term actionSpan =
            k
              (Term itemContext (_context env) (_varSpans env) term)
              (toLineColumns $ Span.absoluteFrom defPos actionSpan)
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
      ) <>
      foreach (Module._imports moduleHeader) (\import_ -> do
        let
          span =
            Module._span import_
        guard $ span `Span.contains` pos
        k (Import (Module._module import_)) $ toLineColumns span
      )

  pure $ case result of
    Left _ ->
      Nothing

    Right result' ->
      result'

data Environment v = Environment
  { _actionPosition :: !Position.Relative
  , _context :: Context v
  , _varSpans :: IntMap Var (NonEmpty Span.Relative)
  }

extend :: Environment v -> Binding -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extend env binding type_ = do
  type' <- lift $ Elaboration.evaluate (_context env) type_
  (context', var) <- lift $ Context.extendUnnamed (_context env) (Binding.toName binding) type'
  pure
    ( env
      { _context = context'
      , _varSpans = maybe identity (IntMap.insert var) (NonEmpty.nonEmpty $ Binding.spans binding) (_varSpans env)
      }
    , var
    )

extendDef :: Environment v -> Binding -> Syntax.Term v -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extendDef env binding term type_ = do
  value <- lift $ Elaboration.evaluate (_context env) term
  type' <- lift $ Elaboration.evaluate (_context env) type_
  (context', var) <- lift $ Context.extendUnnamedDef (_context env) (Binding.toName binding) value type'
  pure
    ( env
      { _context = context'
      , _varSpans = maybe identity (IntMap.insert var) (NonEmpty.nonEmpty $ Binding.spans binding) (_varSpans env)
      }
    , var
    )

type RelativeCallback a =
  forall v. ItemContext -> Environment v -> Syntax.Term v -> Span.Relative -> MaybeT M a

definitionAction
  :: forall a
  . RelativeCallback a
  -> Environment Void
  -> Scope.Key
  -> Name.Qualified
  -> MaybeT M a
definitionAction k env key qualifiedName =
  definitionNameActions <|> do
    (def, _, metaVars) <- MaybeT $ fetch $ Query.ElaboratingDefinition $ Scope.KeyedName key qualifiedName
    metaVarsVar <- liftIO $ newIORef metaVars
    let
      env' =
        env { _context = (_context env) { Context.metas = metaVarsVar } }
    case def of
      Syntax.TypeDeclaration type_ ->
        termAction k env' type_

      Syntax.ConstantDefinition term ->
        termAction k env' term

      Syntax.DataDefinition _ tele ->
        dataDefinitionAction k env' tele
  where
    definitionNameActions :: MaybeT M a
    definitionNameActions = do
      constructorSpans <- Occurrences.definitionConstructorSpans key qualifiedName
      spans <- Occurrences.definitionNameSpans key qualifiedName
      asum $
        foreach constructorSpans (\(span, constr) -> do
          guard $ span `Span.relativeContains` _actionPosition env
          k DefinitionContext env (Syntax.Con constr) span
        ) <>
        foreach spans (\span -> do
          guard $ span `Span.relativeContains` _actionPosition env
          k DefinitionContext env (Syntax.Global qualifiedName) span
        )

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

    Syntax.Int _ ->
      empty

    Syntax.Meta _ ->
      empty

    Syntax.Let binding term' type_ body -> do
      (env', var) <- extendDef env binding term' type_
      bindingAction k env' binding var <|>
        termAction k env term' <|>
        termAction k env type_ <|>
        termAction k env' body

    Syntax.Pi binding domain _ target -> do
      (env', var) <- extend env binding domain
      bindingAction k env' binding var <|>
        termAction k env domain <|>
        termAction k env' target

    Syntax.Fun domain _ target ->
      termAction k env domain <|>
      termAction k env target

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
      branchesAction k env scrutinee branches <|>
      asum (termAction k env <$> defaultBranch)

    Syntax.Spanned span term' ->
      termAction k env term' <|> do
        guard $ span `Span.relativeContains` _actionPosition env
        k ExpressionContext env term' span

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

branchesAction
  :: RelativeCallback a
  -> Environment v
  -> Syntax.Term v
  -> Syntax.Branches v
  -> MaybeT M a
branchesAction k env scrutinee branches =
  case branches of
    Syntax.ConstructorBranches constructorBranches ->
      asum (constructorBranchAction k env scrutinee <$> HashMap.toList constructorBranches)

    Syntax.LiteralBranches literalBranches ->
      asum (literalBranchAction k env <$> HashMap.toList literalBranches)

constructorBranchAction
  :: RelativeCallback a
  -> Environment v
  -> Syntax.Term v
  -> (Name.QualifiedConstructor, ([Span.Relative], Telescope Syntax.Type Syntax.Term v))
  -> MaybeT M a
constructorBranchAction k env scrutinee (constr@(Name.QualifiedConstructor typeName _), (spans, tele)) =
  asum (foreach spans $ \span -> do
      guard $ any (`Span.relativeContains` _actionPosition env) spans
      scrutinee' <- lift $ Elaboration.evaluate (_context env) scrutinee
      scrutineeType <- lift $ TypeOf.typeOf (_context env) scrutinee'
      scrutineeType' <- lift $ Context.forceHead (_context env) scrutineeType
      case scrutineeType' of
        Domain.Neutral (Domain.Global headName) spine
          | headName == typeName -> do
            spine' <- lift $ mapM (mapM $ Elaboration.readback $ _context env) spine
            k PatternContext env (Syntax.Con constr `Syntax.apps` fmap (first implicitise) spine') span

        _ ->
          k PatternContext env (Syntax.Con constr) span
  ) <|>
  teleAction k env tele

literalBranchAction
  :: RelativeCallback a
  -> Environment v
  -> (Integer, ([Span.Relative], Syntax.Term v))
  -> MaybeT M a
literalBranchAction k env (_, (_, body)) =
  -- TODO use literal
  termAction k env body

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
    Binding.Spanned spannedNames ->
      case Context.lookupVarIndex var $ _context env of
        Nothing ->
          empty

        Just index ->
          asum $ foreach spannedNames $ \(span, _) -> do
            guard $ span `Span.relativeContains` _actionPosition env
            k PatternContext env (Syntax.Var index) span

    Binding.Unspanned _ ->
      empty
