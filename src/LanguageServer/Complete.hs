{-# language FlexibleContexts #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
module LanguageServer.Complete where

import Protolude hiding (IntMap, evaluate, moduleName)

import qualified Data.HashMap.Lazy as HashMap
-- import qualified Data.Text.IO as Text
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Language.Haskell.LSP.Types as LSP
import Rock

import Context (Context)
import qualified Context
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Domain
import qualified Elaboration
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import Monad
import Name (Name(Name))
import qualified Name
import qualified Position
import qualified Query
import Query (Query)
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Syntax
import qualified TypeOf
import Var (Var)
import qualified Var

complete :: FilePath -> Position.LineColumn -> Task Query (Maybe [LSP.CompletionItem])
complete filePath pos =
  CursorAction.cursorAction filePath pos $ \context varPositions _ _ -> do
    names <- lift $ getUsableNames context varPositions
    lift $ forM names $ \(name, term, kind) -> do
      value <- Elaboration.evaluate context term
      type_ <- TypeOf.typeOf context value
      type' <- Elaboration.readback context type_
      prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type'
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
          }

questionMark :: FilePath -> Position.LineColumn -> Task Query (Maybe [LSP.CompletionItem])
questionMark filePath (Position.LineColumn line column) =
  CursorAction.cursorAction filePath (Position.LineColumn line $ max 0 $ column - 1) $ \context varPositions termUnderCursor _ -> do
    valueUnderCursor <- lift $ Elaboration.evaluate context termUnderCursor
    typeUnderCursor <- lift $ TypeOf.typeOf context valueUnderCursor
    names <- lift $ getUsableNames context varPositions

    lift $ fmap concat $ forM names $ \(name, term, kind) -> do
      value <- Elaboration.evaluate context term
      type_ <- TypeOf.typeOf context value
      maybeFun <- (Just <$> Elaboration.subtypeWithoutRecovery context type_ typeUnderCursor)
        `catchError` \_ -> pure Nothing

      case maybeFun of
        Nothing -> do
          -- typeUnderCursor' <- Elaboration.readback context typeUnderCursor
          -- type' <- Elaboration.readback context type_
          -- prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type'
          -- prettyTypeUnderCursor <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context typeUnderCursor'
          -- liftIO $ Text.hPutStrLn stderr $ "nothing " <> show prettyType
          -- liftIO $ Text.hPutStrLn stderr $ "nothing toc " <> show prettyTypeUnderCursor
          pure []

        Just fun -> do
          let
            term' =
              fun term
          value' <- Elaboration.evaluate context term'
          type' <- TypeOf.typeOf context value'
          type'' <- Elaboration.readback context type'
          prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type''
          -- liftIO $ Text.hPutStrLn stderr $ show prettyType
          pure $ pure
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
                , _newText = name
                }
              , _additionalTextEdits = Nothing
              , _commitCharacters = Nothing
              , _command = Nothing
              , _xdata = Nothing
              }

getUsableNames :: Context v -> IntMap Var value -> M [(Text, Syntax.Term v, LSP.CompletionItemKind)]
getUsableNames context varPositions = do
  locals <- forM (IntMap.toList varPositions) $ \(var, _) -> do
    let
      Name text =
        Context.lookupVarName var context
    term <- Elaboration.readback context $ Domain.var var
    pure (text, term, LSP.CiVariable)
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

  imports <- forM (HashMap.toList scopeEntries) $ \(Name.Pre name, entry) ->
    case entry of
      Scope.Name global -> do
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

      Scope.Constructors constrs ->
        pure
          [ (name, Syntax.Con con, LSP.CiEnumMember)
          | con <- toList constrs
          ]

      Scope.Ambiguous _ _ ->
        pure []
  pure $ locals <> concat imports
