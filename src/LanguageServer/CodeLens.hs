{-# language OverloadedStrings #-}
module LanguageServer.CodeLens where

import Protolude hiding (IntMap, evaluate, moduleName)

import Data.Text.Prettyprint.Doc (Doc)
import qualified Data.Text.Unsafe as Text
import Rock

import qualified Context
import qualified Error.Hydrated as Error
import qualified LanguageServer.LineColumns as LineColumns
import Monad
import Name (Name(Name))
import qualified Name
import qualified Position
import qualified Presyntax
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

codeLens :: FilePath -> Task Query [(Span.LineColumn, Doc ann)]
codeLens filePath =
  runM $ do
    (moduleName, _, defs) <- fetch $ Query.ParsedFile filePath

    toLineColumns <- LineColumns.fromAbsolute moduleName
    let
      previousDefs =
        Nothing : fmap Just defs
    fmap concat $ forM (zip previousDefs defs) $ \(previousDef, (pos, (name@(Name nameText), def))) -> do
      let
        qualifiedName =
          Name.Qualified moduleName name

        go = do
          context <- Context.empty $ Scope.KeyedName Scope.Definition qualifiedName
          type_ <- fetch $ Query.ElaboratedType qualifiedName
          prettyType <- Error.prettyPrettyableTerm 0 =<< Context.toPrettyableTerm context type_
          pure
            [ ( toLineColumns $ Span.Absolute pos $ pos + Position.Absolute (Text.lengthWord16 nameText)
              , prettyType
              )
            ]

      case (previousDef, def) of
        (Just (_, (previousName, Presyntax.TypeDeclaration {})), _)
          | previousName == name ->
            pure []

        (_, Presyntax.TypeDeclaration {}) ->
          pure []

        (_, Presyntax.ConstantDefinition {}) ->
          go

        (_, Presyntax.DataDefinition {}) ->
          go
