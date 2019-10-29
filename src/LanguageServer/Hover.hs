{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.Hover where

import Protolude hiding (evaluate, moduleName)

import Data.Text.Prettyprint.Doc (Doc, (<+>))
import Rock

import qualified Context
import qualified Elaboration
import qualified Error.Hydrated as Error
import qualified Position
import Query (Query)
import qualified Span
import qualified TypeOf
import qualified LanguageServer.CursorAction as CursorAction

hover :: FilePath -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath pos = do
  CursorAction.cursorAction filePath pos CursorAction.Elaborated $ \context _ term lineColumn -> do
    value <- lift $ Elaboration.evaluate context term
    type_ <- lift $ TypeOf.typeOf context value
    type' <- lift $ Elaboration.readback context type_
    prettyTerm <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context term
    prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type'
    pure
      ( lineColumn
      , prettyTerm <+> ":" <+> prettyType
      )
