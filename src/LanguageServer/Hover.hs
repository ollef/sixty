{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.Hover where

import Protolude hiding (evaluate, moduleName)

import Data.Text.Prettyprint.Doc (Doc, (<+>))
import Rock

import qualified Context
import qualified Elaboration
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import qualified Position
import Query (Query)
import qualified Span
import qualified TypeOf

hover :: FilePath -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath pos = do
  CursorAction.cursorAction filePath pos $ \item lineColumn ->
    case item of
      CursorAction.Term _ context _ term -> do
        value <- lift $ Elaboration.evaluate context term
        type_ <- lift $ TypeOf.typeOf context value
        type' <- lift $ Elaboration.readback context type_
        prettyTerm <- Error.prettyPrettyableTerm 0 =<< lift (Context.toPrettyableTerm context term)
        prettyType <- Error.prettyPrettyableTerm 0 =<< lift (Context.toPrettyableTerm context type')
        pure
          ( lineColumn
          , prettyTerm <+> ":" <+> prettyType
          )

      CursorAction.Import _ ->
        empty
