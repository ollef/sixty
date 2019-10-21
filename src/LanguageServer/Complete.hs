{-# language FlexibleContexts #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
module LanguageServer.Complete where

import Protolude hiding (evaluate, moduleName)

import qualified Data.HashMap.Lazy as HashMap
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Language.Haskell.LSP.Types as LSP
import Rock

import qualified Context
import qualified Data.IntMap as IntMap
import qualified Domain
import qualified Elaboration
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import Name (Name(Name))
import qualified Name
import qualified Position
import qualified Query
import Query (Query)
import qualified Query.Mapped as Mapped
import qualified Scope
import qualified Syntax
import qualified TypeOf
import qualified Var

complete :: FilePath -> Position.LineColumn -> Task Query (Maybe [LSP.CompletionItem])
complete filePath pos = do
  CursorAction.cursorAction filePath pos $ \context varPositions _ _ -> do
    locals <- lift $ forM (IntMap.toList varPositions) $ \(var, _) -> do
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

    imports <- lift $ forM (HashMap.toList scopeEntries) $ \(Name.Pre name, entry) ->
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

    lift $ forM (locals <> concat imports) $ \(name, term, kind) -> do
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
