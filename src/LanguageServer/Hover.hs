{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Hover where

import qualified Core.TypeOf as TypeOf
import qualified Elaboration
import qualified Elaboration.Context as Context
import qualified Error.Hydrated as Error
import qualified LanguageServer.CursorAction as CursorAction
import qualified Position
import Prettyprinter (Doc, (<+>))
import Protolude hiding (evaluate, moduleName)
import Query (Query)
import Rock
import qualified Span

hover :: FilePath -> Position.LineColumn -> Task Query (Maybe (Span.LineColumn, Doc ann))
hover filePath pos =
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
