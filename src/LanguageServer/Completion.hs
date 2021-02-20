{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module LanguageServer.Completion where

import Protolude hiding (IntMap, catch, evaluate, moduleName)

import Control.Exception.Lifted
import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef.Lifted
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Language.Haskell.LSP.Types as LSP
import Rock

import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Core.TypeOf as TypeOf
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Elaboration
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Error
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import Monad
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Position
import qualified Query
import Query (Query)
import qualified Query.Mapped as Mapped
import qualified Scope
import Var (Var)
import qualified Var

complete :: FilePath -> Position.LineColumn -> Task Query (Maybe [LSP.CompletionItem])
complete filePath (Position.LineColumn line column) =
  CursorAction.cursorAction filePath (Position.LineColumn line $ max 0 $ column - 1) $ \item _ ->
    case item of
      CursorAction.Import _ ->
        empty

      CursorAction.Term itemContext context varPositions _ -> do
        names <- lift $ getUsableNames itemContext context varPositions
        lift $ forM names $ \(name, term, kind) -> do
          value <- Elaboration.evaluate context term
          type_ <- TypeOf.typeOf context value
          type' <- Elaboration.readback context type_
          prettyType <- Error.prettyPrettyableTerm 0 =<< Context.toPrettyableTerm context type'
          pure
            LSP.CompletionItem
              { _label = name
              , _kind = Just kind
              , _detail = Just $ show $ ":" <+> prettyType
              , _documentation = Nothing
              , _deprecated = Nothing
              , _preselect = Nothing
              , _sortText = Nothing
              , _filterText = Nothing
              , _insertText = Nothing
              , _insertTextFormat = Nothing
              , _textEdit = Nothing
              , _additionalTextEdits = Nothing
              , _commitCharacters = Nothing
              , _command = Nothing
              , _xdata = Nothing
              , _tags = mempty
              }

questionMark :: FilePath -> Position.LineColumn -> Task Query (Maybe [LSP.CompletionItem])
questionMark filePath (Position.LineColumn line column) =
  CursorAction.cursorAction filePath (Position.LineColumn line $ max 0 $ column - 1) $ \item _ ->
    case item of
      CursorAction.Import _ ->
        empty

      CursorAction.Term itemContext context varPositions termUnderCursor -> do
        valueUnderCursor <- lift $ Elaboration.evaluate context termUnderCursor
        typeUnderCursor <- lift $ TypeOf.typeOf context valueUnderCursor
        typeUnderCursor' <- lift $ Elaboration.readback context typeUnderCursor
        prettyTypeUnderCursor <- lift $ Error.prettyPrettyableTerm 0 =<< Context.toPrettyableTerm context typeUnderCursor'
        names <- lift $ getUsableNames itemContext context varPositions

        metasBefore <- readIORef $ Context.metas context
        lift $ fmap concat $ forM names $ \(name, term, kind) -> do
          writeIORef (Context.metas context) metasBefore
          value <- Elaboration.evaluate context term
          type_ <- TypeOf.typeOf context value
          (maxArgs, _) <- Elaboration.insertMetas context Elaboration.UntilTheEnd type_
          metasBefore' <- readIORef $ Context.metas context
          maybeArgs <- runMaybeT $ asum $ foreach (inits maxArgs) $ \args -> do
            writeIORef (Context.metas context) metasBefore'
            appliedValue <- lift $ foldM (\fun (plicity, arg) -> Evaluation.apply fun plicity arg) value args
            appliedType <- lift $ TypeOf.typeOf context appliedValue
            _ <- MaybeT $
              (Just <$> Elaboration.subtypeWithoutRecovery context appliedType typeUnderCursor)
              `catch` \(_ :: Error.Elaboration) -> pure Nothing
            pure args


          pure $ case maybeArgs of
            Nothing ->
              -- typeUnderCursor' <- Elaboration.readback context typeUnderCursor
              -- type' <- Elaboration.readback context type_
              -- prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type'
              -- prettyTypeUnderCursor <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context typeUnderCursor'
              -- Text.hPutStrLn stderr $ "nothing " <> show prettyType
              -- Text.hPutStrLn stderr $ "nothing toc " <> show prettyTypeUnderCursor
              []

            Just args -> do
              let
                explicitArgs =
                  filter ((== Explicit) . fst) args
              pure
                LSP.CompletionItem
                  { _label = name
                  , _kind = Just kind
                  , _detail = Just $ show $ ":" <+> prettyTypeUnderCursor
                  , _documentation = Nothing
                  , _deprecated = Nothing
                  , _preselect = Nothing
                  , _sortText = Nothing
                  , _filterText = Nothing
                  , _insertText = Nothing
                  , _insertTextFormat = Just LSP.Snippet
                  , _textEdit = Just LSP.TextEdit
                    { _range =
                      LSP.Range
                        { _start = LSP.Position
                          { _line = line
                          , _character = column - 1
                          }
                        , _end = LSP.Position
                          { _line = line
                          , _character = column
                          }
                        }
                        , _newText =
                          (if null explicitArgs then "" else "(") <>
                          name <>
                          mconcat
                          [" ${" <> show (n :: Int) <> ":?}"
                          | (n, _) <- zip [1..] explicitArgs
                          ] <>
                          (if null explicitArgs then "" else ")")
                    }
                  , _additionalTextEdits = Nothing
                  , _commitCharacters = Nothing
                  , _command = Nothing
                  , _xdata = Nothing
                  , _tags = mempty
                  }

getUsableNames :: CursorAction.ItemContext -> Context v -> IntMap Var value -> M [(Text, Syntax.Term v, LSP.CompletionItemKind)]
getUsableNames itemContext context varPositions = do
  hPutStrLn stderr $ "getUsableNames " ++ show itemContext
  locals <- case itemContext of
    CursorAction.ExpressionContext ->
      forM (IntMap.toList varPositions) $ \(var, _) -> do
        let
          Name text =
            Context.lookupVarName var context
        term <- Elaboration.readback context $ Domain.var var
        pure (text, term, LSP.CiVariable)

    CursorAction.PatternContext ->
      pure []

    CursorAction.DefinitionContext ->
      pure []

  let
    Scope.KeyedName key (Name.Qualified module_ keyName) =
      Context.scopeKey context
  (_, scopes) <- fetch $ Query.Scopes module_
  importedScopeEntries <- fetch $ Query.ImportedNames module_ Mapped.Map
  let
    (moduleScopeEntries, _) =
      HashMap.lookupDefault mempty (keyName, key) scopes

    scopeEntries =
      moduleScopeEntries <> importedScopeEntries

  imports <- forM (HashMap.toList scopeEntries) $ \(Name.Surface name, entry) ->
    case entry of
      Scope.Name global -> do
        let
          go = do
            maybeDefinition <- fetch $ Query.ElaboratedDefinition global
            pure
              [ ( name
                , Syntax.Global global
                , case maybeDefinition of
                    Just (Syntax.DataDefinition {}, _) ->
                      LSP.CiEnum

                    Just (Syntax.ConstantDefinition {}, _) ->
                      LSP.CiConstant

                    Just (Syntax.TypeDeclaration {}, _) ->
                      LSP.CiConstant

                    Nothing ->
                      LSP.CiConstant
                )
              ]
        case itemContext of
          CursorAction.ExpressionContext ->
            go

          CursorAction.PatternContext ->
            pure []

          CursorAction.DefinitionContext ->
            go

      Scope.Constructors constrs datas -> do
        let
          go =
            pure $
              case toList datas of
                [data_] ->
                  [(name, Syntax.Global data_, LSP.CiEnum)]

                _ ->
                  []
              <>
              [ (name, Syntax.Con con, LSP.CiEnumMember)
              | con <- toList constrs
              ]
        case itemContext of
          CursorAction.ExpressionContext ->
            go

          CursorAction.PatternContext ->
            go

          CursorAction.DefinitionContext ->
            pure []

      Scope.Ambiguous _ _ ->
        pure []
  pure $ locals <> concat imports
