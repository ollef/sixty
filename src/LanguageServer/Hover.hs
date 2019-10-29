{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module LanguageServer.Hover where

import Protolude hiding (evaluate, moduleName)

import Data.IORef
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
  CursorAction.cursorAction filePath pos CursorAction.Elaborating $ \context _ term lineColumn -> do
    value <- lift $ Elaboration.evaluate context term
    type_ <- lift $ TypeOf.typeOf context value
    type' <- lift $ Elaboration.readback context type_
    metaVars <- liftIO $ newIORef mempty
    term' <- lift $ CursorAction.zonk context metaVars term
    type'' <- lift $ CursorAction.zonk context metaVars type'
    prettyTerm <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context term'
    prettyType <- Error.prettyPrettyableTerm 0 $ Context.toPrettyableTerm context type''
    pure
      ( lineColumn
      , prettyTerm <+> ":" <+> prettyType
      )
