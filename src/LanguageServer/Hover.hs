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
import qualified Domain
import qualified Elaboration
import Index
import Monad
import Name (Name)
import qualified Name
import qualified Position
import qualified Pretty
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified TypeOf

data Environment v = Environment
  { _prettyEnvironment :: Pretty.Environment v
  , _context :: Context v
  }

extend :: Environment v -> Name -> Domain.Type -> M (Environment (Succ v))
extend env name type_ = do
  let
    (prettyEnv, _) =
      Pretty.extend (_prettyEnvironment env) name

  (context, _) <- Context.extendUnnamed (_context env) name type_
  pure Environment
    { _prettyEnvironment = prettyEnv
    , _context = context
    }

hover :: FilePath -> Text -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath contents (Position.LineColumn line column) = do
  (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
  spans <- fetch $ Query.ModuleSpanMap moduleName
  prettyEnv <- Pretty.emptyM moduleName
  results <- forM (HashMap.toList spans) $ \((key, name), span@(Span.Absolute defPos _)) ->
    if span `Span.contains` pos then do
      let
        qualifiedName =
          Name.Qualified moduleName name
      context <- Context.empty $ Scope.KeyedName key qualifiedName
      let
        env =
          Environment
            { _prettyEnvironment = prettyEnv
            , _context = context
            }
      maybeResult <- hoverDefinition (Position.relativeTo defPos pos) env key qualifiedName
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
  -> Environment Void
  -> Scope.Key
  -> Name.Qualified
  -> Task Query (Maybe (Span.Relative, Doc ann))
hoverDefinition pos env key name = do
  result <-
    runM $
    runMaybeT $
      case key of
        Scope.Type -> do
          type_ <- fetch $ Query.ElaboratedType name
          hoverTerm pos env type_

        Scope.Definition -> do
          maybeDef <- fetch $ Query.ElaboratedDefinition name
          case maybeDef of
            Nothing ->
              empty

            Just (def, _) ->
              case def of
                Syntax.TypeDeclaration type_ ->
                  hoverTerm pos env type_

                Syntax.ConstantDefinition term ->
                  hoverTerm pos env term

                Syntax.DataDefinition tele ->
                  hoverDataDefinition pos env tele
  case result of
    Left _ ->
      pure Nothing

    Right res ->
      pure res

hoverTerm
  :: Position.Relative
  -> Environment v
  -> Syntax.Term v
  -> MaybeT M (Span.Relative, Doc ann)
hoverTerm pos env term =
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
      type' <- lift $ evaluate env type_
      env' <- lift $ extend env name type'
      hoverTerm pos env term' <|>
        hoverTerm pos env type_ <|>
        hoverTerm pos env' body

    Syntax.Pi name source _ domain -> do
      source' <- lift $ evaluate env source
      env' <- lift $ extend env name source'
      hoverTerm pos env source <|>
        hoverTerm pos env' domain

    Syntax.Fun source domain ->
      hoverTerm pos env source <|>
      hoverTerm pos env domain

    Syntax.Lam name type_ _ body -> do
      type' <- lift $ evaluate env type_
      env' <- lift $ extend env name type'
      hoverTerm pos env type_ <|>
        hoverTerm pos env' body

    Syntax.App t1 _ t2 ->
      hoverTerm pos env t1 <|>
      hoverTerm pos env t2

    Syntax.Case scrutinee branches defaultBranch ->
      hoverTerm pos env scrutinee <|>
      asum (hoverBranch pos env <$> HashMap.elems branches) <|>
      asum (hoverTerm pos env <$> defaultBranch)

    Syntax.Spanned span term' ->
      hoverTerm pos env term' <|>
      if span `Span.relativeContains` pos then do
        term'' <- lift $ Elaboration.evaluate (_context env) term'
        type_ <- lift $ TypeOf.typeOf (_context env) term''
        type' <- lift $ Elaboration.readback (_context env) type_
        pure
          ( span
          , Pretty.prettyTerm 0 (_prettyEnvironment env) term' <+> ":" <+>
            Pretty.prettyTerm 0 (_prettyEnvironment env) type'
          )

      else
        empty

hoverDataDefinition
  :: Position.Relative
  -> Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> MaybeT M (Span.Relative, Doc ann)
hoverDataDefinition pos env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrDefs) ->
      asum $ hoverTerm pos env <$> HashMap.elems constrDefs

    Telescope.Extend name type_ _ tele' -> do
      type' <- lift $ evaluate env type_
      env' <- lift $ extend env name type'
      hoverTerm pos env type_ <|>
        hoverDataDefinition pos env' tele'

hoverBranch
  :: Position.Relative
  -> Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> MaybeT M (Span.Relative, Doc ann)
hoverBranch pos env tele =
  case tele of
    Telescope.Empty branch ->
      hoverTerm pos env branch

    Telescope.Extend name type_ _ tele' -> do
      type' <- lift $ evaluate env type_
      env' <- lift $ extend env name type'
      hoverTerm pos env type_ <|>
        hoverBranch pos env' tele'

evaluate :: Environment v -> Syntax.Term v -> M Domain.Value
evaluate env =
  Elaboration.evaluate (_context env)
