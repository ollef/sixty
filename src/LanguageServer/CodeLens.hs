{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.CodeLens where

import qualified Data.Text.Unsafe as Text
import qualified Elaboration.Context as Context
import qualified Error.Hydrated as Error
import qualified LanguageServer.LineColumns as LineColumns
import Monad
import Name (Name (Name))
import qualified Name
import qualified Position
import Prettyprinter (Doc)
import Protolude hiding (IntMap, evaluate, moduleName)
import Query (Query)
import qualified Query
import Rock
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import qualified UTF16

codeLens :: FilePath -> Task Query [(UTF16.LineColumns, Doc ann)]
codeLens filePath =
  runM $ do
    (moduleName, _, defs) <- fetch $ Query.ParsedFile filePath

    toLineColumns <- LineColumns.fromAbsolute moduleName
    let previousDefs =
          Nothing : fmap Just defs
    fmap concat $
      forM (zip previousDefs defs) \(previousDef, (pos, (name@(Name nameText), def))) -> do
        let qualifiedName =
              Name.Qualified moduleName name

            go = do
              context <- Context.empty Scope.Definition qualifiedName
              type_ <- fetch $ Query.ElaboratedType qualifiedName
              prettyType <- Error.prettyPrettyableTerm 0 =<< Context.toPrettyableTerm context type_
              pure
                [
                  ( toLineColumns $ Span.Absolute pos $ pos + Position.Absolute (Text.lengthWord8 nameText)
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
