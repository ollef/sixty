{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.Hover where

import Protolude hiding (evaluate, moduleName)

import Data.Text.Prettyprint.Doc (Doc, (<+>))
import Rock

import qualified Elaboration.Context as Context
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import qualified Position
import Query (Query)
import qualified Span
import qualified Core.TypeOf2 as TypeOf

hover :: FilePath -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath pos =
  CursorAction.cursorAction filePath pos $ \item lineColumn ->
    case item of
      CursorAction.Term _ context _ term -> do
        type_ <- lift $ TypeOf.typeOf context term
        prettyTerm <- Error.prettyPrettyableTerm 0 =<< lift (Context.toPrettyableTerm context term)
        prettyType <- Error.prettyPrettyableTerm 0 =<< lift (Context.toPrettyableTerm context type_)
        pure
          ( lineColumn
          , prettyTerm <+> ":" <+> prettyType
          )

      CursorAction.Import _ ->
        empty
