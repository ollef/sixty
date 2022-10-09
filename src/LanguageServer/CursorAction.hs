{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module LanguageServer.CursorAction where

import Control.Monad.Trans.Maybe
import Core.Binding (Binding)
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Syntax as Syntax
import qualified Core.TypeOf as TypeOf
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef.Lifted
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Text.Utf16.Rope as Rope
import qualified Elaboration
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Elaboration.Meta as Meta
import qualified Index
import qualified LanguageServer.LineColumns as LineColumns
import Literal (Literal)
import qualified Module
import Monad
import Name (Name)
import qualified Name
import qualified Occurrences
import Plicity
import qualified Position
import Protolude hiding (evaluate, moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import qualified Span
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

type Callback a = ItemUnderCursor -> Span.LineColumn -> MaybeT M a

data ItemUnderCursor where
  Term ::
    ItemContext ->
    Context v ->
    EnumMap Var (NonEmpty Span.Relative) ->
    Syntax.Term v ->
    ItemUnderCursor
  Import ::
    Name.Module ->
    ItemUnderCursor

data ItemContext
  = ExpressionContext
  | PatternContext
  | DefinitionContext
  deriving (Show)

cursorAction ::
  forall a.
  FilePath ->
  Position.LineColumn ->
  Callback a ->
  Task Query (Maybe a)
cursorAction filePath (Position.LineColumn line column) k =
  runM $
    runMaybeT $ do
      (moduleName, moduleHeader, _) <- fetch $ Query.ParsedFile filePath
      spans <- fetch $ Query.ModuleSpanMap moduleName
      contents <- fetch $ Query.FileText filePath
      let -- TODO use the rope that we get from the LSP library instead
          pos =
            Position.Absolute $
              case Rope.splitAtPosition (Rope.Position (fromIntegral line) (fromIntegral column)) $ Rope.fromText contents of
                Nothing -> 0
                Just (rope, _) -> fromIntegral $ Rope.length rope

      toLineColumns <- LineColumns.fromAbsolute moduleName
      asum $
        foreach
          (HashMap.toList spans)
          ( \((definitionKind, name), span@(Span.Absolute defPos _)) -> do
              guard $ span `Span.contains` pos
              let qualifiedName =
                    Name.Qualified moduleName name

                  k' :: RelativeCallback a
                  k' itemContext env term actionSpan =
                    k
                      (Term itemContext (_context env) (_varSpans env) term)
                      (toLineColumns $ Span.absoluteFrom defPos actionSpan)
              context <- Context.empty definitionKind qualifiedName
              definitionAction
                k'
                Environment
                  { _actionPosition = Position.relativeTo defPos pos
                  , _context = context
                  , _varSpans = mempty
                  }
                definitionKind
                qualifiedName
          )
          <> foreach
            (Module._imports moduleHeader)
            ( \import_ -> do
                let span =
                      Module._span import_
                guard $ span `Span.contains` pos
                k (Import (Module._module import_)) $ toLineColumns span
            )

data Environment v = Environment
  { _actionPosition :: !Position.Relative
  , _context :: Context v
  , _varSpans :: EnumMap Var (NonEmpty Span.Relative)
  }

extendBinding :: Environment v -> Binding -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extendBinding env binding =
  extend env (Binding.toName binding) (Binding.spans binding)

extendBindings :: Environment v -> Bindings -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extendBindings env bindings =
  extend env (Bindings.toName bindings) (Bindings.spans bindings)

extend :: Environment v -> Name -> [Span.Relative] -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extend env name spans type_ = do
  type' <- lift $ Elaboration.evaluate (_context env) type_
  (context', var) <- lift $ Context.extend (_context env) name type'
  pure
    ( env
        { _context = context'
        , _varSpans = maybe identity (EnumMap.insert var) (NonEmpty.nonEmpty spans) (_varSpans env)
        }
    , var
    )

extendDef :: Environment v -> Bindings -> Syntax.Term v -> Syntax.Type v -> MaybeT M (Environment (Index.Succ v), Var)
extendDef env bindings term type_ = do
  value <- lift $ Elaboration.evaluate (_context env) term
  type' <- lift $ Elaboration.evaluate (_context env) type_
  (context', var) <- lift $ Context.extendDef (_context env) (Bindings.toName bindings) value type'
  pure
    ( env
        { _context = context'
        , _varSpans = maybe identity (EnumMap.insert var) (NonEmpty.nonEmpty $ Bindings.spans bindings) (_varSpans env)
        }
    , var
    )

type RelativeCallback a =
  forall v. ItemContext -> Environment v -> Syntax.Term v -> Span.Relative -> MaybeT M a

definitionAction ::
  forall a.
  RelativeCallback a ->
  Environment Void ->
  Scope.DefinitionKind ->
  Name.Qualified ->
  MaybeT M a
definitionAction k env definitionKind qualifiedName =
  definitionNameActions <|> do
    (def, _, metaVars) <- MaybeT $ fetch $ Query.ElaboratingDefinition definitionKind qualifiedName
    metaVarsVar <- newIORef $ Meta.fromEagerState metaVars
    let env' =
          env {_context = (_context env) {Context.metas = metaVarsVar}}
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
      constructorSpans <- Occurrences.definitionConstructorSpans definitionKind qualifiedName
      spans <- Occurrences.definitionNameSpans definitionKind qualifiedName
      asum $
        foreach
          constructorSpans
          ( \(span, constr) -> do
              guard $ span `Span.relativeContains` _actionPosition env
              k DefinitionContext env (Syntax.Con constr) span
          )
          <> foreach
            spans
            ( \span -> do
                guard $ span `Span.relativeContains` _actionPosition env
                k DefinitionContext env (Syntax.Global qualifiedName) span
            )

termAction ::
  RelativeCallback a ->
  Environment v ->
  Syntax.Term v ->
  MaybeT M a
termAction k env term =
  case term of
    Syntax.Var _ ->
      empty
    Syntax.Global _ ->
      empty
    Syntax.Con _ ->
      empty
    Syntax.Lit _ ->
      empty
    Syntax.Meta _ ->
      empty
    Syntax.PostponedCheck {} ->
      empty
    Syntax.Lets lets ->
      letsAction k env lets
    Syntax.Pi binding domain _ target -> do
      (env', var) <- extendBinding env binding domain
      bindingAction k env' binding var
        <|> termAction k env domain
        <|> termAction k env' target
    Syntax.Fun domain _ target ->
      termAction k env domain
        <|> termAction k env target
    Syntax.Lam bindings type_ _ body -> do
      (env', var) <- extendBindings env bindings type_
      bindingsAction k env' bindings var
        <|> termAction k env type_
        <|> termAction k env' body
    Syntax.App t1 _ t2 ->
      termAction k env t1
        <|> termAction k env t2
    Syntax.Case scrutinee branches defaultBranch ->
      termAction k env scrutinee
        <|> branchesAction k env scrutinee branches
        <|> asum (termAction k env <$> defaultBranch)
    Syntax.Spanned span term' ->
      termAction k env term' <|> do
        guard $ span `Span.relativeContains` _actionPosition env
        k ExpressionContext env term' span

letsAction :: RelativeCallback a -> Environment v -> Syntax.Lets v -> MaybeT M a
letsAction k env lets =
  case lets of
    Syntax.LetType binding type_ lets' -> do
      (env', var) <- extendBinding env binding type_
      bindingAction k env' binding var
        <|> termAction k env type_
        <|> letsAction k env' lets'
    Syntax.Let bindings index term lets' ->
      definingBindingsAction k env bindings (Context.lookupIndexVar index $ _context env)
        <|> termAction k env term
        <|> letsAction k env lets'
    Syntax.In term ->
      termAction k env term

dataDefinitionAction ::
  RelativeCallback a ->
  Environment v ->
  Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v ->
  MaybeT M a
dataDefinitionAction k env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      asum $ termAction k env <$> OrderedHashMap.elems constrDefs
    Telescope.Extend binding type_ _ tele' -> do
      (env', var) <- extendBinding env binding type_
      bindingAction k env' binding var
        <|> termAction k env type_
        <|> dataDefinitionAction k env' tele'

branchesAction ::
  RelativeCallback a ->
  Environment v ->
  Syntax.Term v ->
  Syntax.Branches v ->
  MaybeT M a
branchesAction k env scrutinee branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      asum (constructorBranchAction k env constructorTypeName scrutinee <$> OrderedHashMap.toList constructorBranches)
    Syntax.LiteralBranches literalBranches ->
      asum (literalBranchAction k env <$> OrderedHashMap.toList literalBranches)

constructorBranchAction ::
  RelativeCallback a ->
  Environment v ->
  Name.Qualified ->
  Syntax.Term v ->
  (Name.Constructor, ([Span.Relative], Telescope Bindings Syntax.Type Syntax.Term v)) ->
  MaybeT M a
constructorBranchAction k env typeName scrutinee (constr, (spans, tele)) =
  asum
    ( foreach spans $ \span -> do
        guard $ any (`Span.relativeContains` _actionPosition env) spans
        scrutinee' <- lift $ Elaboration.evaluate (_context env) scrutinee
        scrutineeType <- lift $ TypeOf.typeOf (_context env) scrutinee'
        scrutineeType' <- lift $ Context.forceHead (_context env) scrutineeType
        case scrutineeType' of
          Domain.Neutral (Domain.Global headName) (Domain.appsView -> Just args)
            | headName == typeName -> do
              args' <- lift $ mapM (mapM $ Elaboration.readback $ _context env) args
              k PatternContext env (Syntax.Con qualifiedConstr `Syntax.apps` fmap (first implicitise) args') span
          _ ->
            k PatternContext env (Syntax.Con qualifiedConstr) span
    )
    <|> teleAction k env tele
  where
    qualifiedConstr =
      Name.QualifiedConstructor typeName constr

literalBranchAction ::
  RelativeCallback a ->
  Environment v ->
  (Literal, ([Span.Relative], Syntax.Term v)) ->
  MaybeT M a
literalBranchAction k env (_, (_, body)) =
  -- TODO use literal
  termAction k env body

teleAction ::
  RelativeCallback a ->
  Environment v ->
  Telescope Bindings Syntax.Type Syntax.Term v ->
  MaybeT M a
teleAction k env tele =
  case tele of
    Telescope.Empty branch ->
      termAction k env branch
    Telescope.Extend bindings type_ _ tele' -> do
      (env', var) <- extendBindings env bindings type_
      bindingsAction k env' bindings var
        <|> termAction k env type_
        <|> teleAction k env' tele'

bindingAction ::
  RelativeCallback a ->
  Environment (Index.Succ v) ->
  Binding ->
  Var ->
  MaybeT M a
bindingAction k env binding var =
  case binding of
    Binding.Spanned span _ ->
      case Context.lookupVarIndex var $ _context env of
        Nothing ->
          empty
        Just index -> do
          guard $ span `Span.relativeContains` _actionPosition env
          k PatternContext env (Syntax.Var index) span
    Binding.Unspanned _ ->
      empty

bindingsAction ::
  RelativeCallback a ->
  Environment (Index.Succ v) ->
  Bindings ->
  Var ->
  MaybeT M a
bindingsAction =
  definingBindingsAction

definingBindingsAction ::
  RelativeCallback a ->
  Environment v ->
  Bindings ->
  Var ->
  MaybeT M a
definingBindingsAction k env binding var =
  case binding of
    Bindings.Spanned spannedNames ->
      case Context.lookupVarIndex var $ _context env of
        Nothing ->
          empty
        Just index ->
          asum $
            foreach spannedNames $ \(span, _) -> do
              guard $ span `Span.relativeContains` _actionPosition env
              k PatternContext env (Syntax.Var index) span
    Bindings.Unspanned _ ->
      empty
