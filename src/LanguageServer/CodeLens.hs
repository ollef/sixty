{-# language OverloadedStrings #-}
module LanguageServer.CodeLens where

import Protolude hiding (IntMap, evaluate, moduleName)

import Data.Text.Prettyprint.Doc (Doc)
import Rock

import qualified Data.ByteString as ByteString
import qualified Elaboration.Context as Context
import qualified Error.Hydrated as Error
import qualified LanguageServer.LineColumns as LineColumns
import Monad
import Name (Name(Name))
import qualified Name
import qualified Position
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface

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
            [ ( toLineColumns $ Span.Absolute pos $ pos + Position.Absolute (ByteString.length nameText)
              , prettyType
              )
            ]

      case (previousDef, def) of
        (Just (_, (previousName, Surface.TypeDeclaration {})), _)
          | previousName == name ->
            pure []

        (_, Surface.TypeDeclaration {}) ->
          pure []

        (_, Surface.ConstantDefinition {}) ->
          go

        (_, Surface.DataDefinition {}) ->
          go
