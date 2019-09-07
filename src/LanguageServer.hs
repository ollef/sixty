{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LanguageServer where

import Protolude hiding (state)

import Control.Concurrent.STM as STM
import Control.Lens
import Data.Default (def)
import qualified Data.Rope.UTF16 as Rope
import Data.Text (Text)
import qualified Data.Text.IO as Text
import Data.Text.Prettyprint.Doc (Doc)
import qualified Data.Text.Prettyprint.Doc as Doc
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.Diagnostics as LSP
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import qualified Language.Haskell.LSP.Types.Lens as LSP
import qualified Language.Haskell.LSP.VFS as LSP
import Rock (Task)

import qualified Driver
import qualified Error.Hydrated as Error (Hydrated)
import qualified Error.Hydrated
import qualified Position
import qualified LanguageServer.Hover as Hover
import Query (Query)
import qualified Span

run :: IO ()
run = do
  messageQueue <- newTQueueIO
  _ <- LSP.run
    LSP.InitializeCallbacks
      { LSP.onInitialConfiguration = \_ -> Right ()
      , LSP.onConfigurationChange = \_ -> Right ()
      , LSP.onStartup = \lf -> do
        _ <- forkIO $ messagePump lf $ atomically $ readTQueue messageQueue
        pure Nothing
      }
    (handlers $ atomically . writeTQueue messageQueue)
    options
    Nothing -- (Just "sixten-lsp.log")
  pure ()

handlers :: (LSP.FromClientMessage -> IO ()) -> LSP.Handlers
handlers sendMessage =
  def
    { LSP.initializedHandler = Just $ sendMessage . LSP.NotInitialized
    , LSP.didOpenTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidOpenTextDocument
    , LSP.didSaveTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidSaveTextDocument
    , LSP.didChangeTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidChangeTextDocument
    , LSP.didCloseTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidCloseTextDocument
    , LSP.hoverHandler = Just $ sendMessage . LSP.ReqHover
    }

options :: LSP.Options
options = def
  { Language.Haskell.LSP.Core.textDocumentSync = Just $ LSP.TextDocumentSyncOptions
    { LSP._openClose = Just True
    , LSP._change = Just LSP.TdSyncIncremental
    , LSP._willSave = Just False
    , LSP._willSaveWaitUntil = Just False
    , LSP._save = Just $ LSP.SaveOptions $ Just False
    }
  }

messagePump :: LSP.LspFuncs () -> IO LSP.FromClientMessage -> IO ()
messagePump lf receiveMessage = do
  state <- Driver.initialState
  forever $ do
    message <- receiveMessage
    case message of
      LSP.NotInitialized _ ->
        pure ()

      LSP.NotDidOpenTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidOpenTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        checkAllAndPublishDiagnostics lf state document (Just version)

      LSP.NotDidChangeTextDocument notification -> do
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version

        sendNotification lf $ "messagePump:processing NotDidChangeTextDocument: uri=" <> show document
        checkAllAndPublishDiagnostics lf state document version

      LSP.NotDidSaveTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidSaveTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        checkAllAndPublishDiagnostics lf state document Nothing

      LSP.ReqHover req -> do
        sendNotification lf $ "messagePump: HoverRequest: " <> show req
        let
          LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier document)
            (LSP.Position line char)
              = req ^. LSP.params

        (_, contents) <- fileContents lf document
        (maybeAnnotation, _) <- runTask state document contents Driver.Don'tPrune $
          Hover.hover (toS $ LSP.getUri document) contents (Position.LineColumn line char)

        let
          response =
            foreach maybeAnnotation $
              \(Span.LineColumns (Position.LineColumn startLine startColumn) (Position.LineColumn endLine endColumn), doc) ->
                LSP.Hover
                  { _contents = LSP.HoverContents LSP.MarkupContent
                    { _kind = LSP.MkPlainText
                    , _value = show doc
                    }
                  , _range = Just LSP.Range
                    { LSP._start = LSP.Position
                      { _line = startLine
                      , _character = startColumn
                      }
                    , LSP._end = LSP.Position
                      { _line = endLine
                      , _character = endColumn
                      }
                    }
                  }

        LSP.sendFunc lf $ LSP.RspHover $ LSP.makeResponseMessage req response

      _ ->
        pure ()

-------------------------------------------------------------------------------

checkAllAndPublishDiagnostics
  :: forall ann
  . LSP.LspFuncs ()
  -> Driver.State (Error.Hydrated, Doc ann)
  -> LSP.Uri
  -> LSP.TextDocumentVersion
  -> IO ()
checkAllAndPublishDiagnostics lf state document version =
  withContentsWhenUpToDate lf document version $ \contents -> do
    (_, errors) <- runTask state document contents Driver.Prune $ Driver.checkAll [toS $ LSP.getUri document]
    LSP.publishDiagnosticsFunc lf (length errors) (LSP.toNormalizedUri document) version
      $ LSP.partitionBySource $ errorToDiagnostic <$> errors

runTask
  :: forall a ann
  . Driver.State (Error.Hydrated, Doc ann)
  -> LSP.Uri
  -> Text
  -> Driver.Prune
  -> Task Query a
  -> IO (a, [(Error.Hydrated, Doc ann)])
runTask state document contents prune task = do
  let
    prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
    prettyError err = do
      (heading, body) <- Error.Hydrated.headingAndBody $ Error.Hydrated._error err
      pure (err, heading <> Doc.line <> body)

  Driver.runIncrementalTask state (toS $ LSP.getUri document) contents prettyError prune task

-------------------------------------------------------------------------------

sendNotification :: LSP.LspFuncs () -> Text -> IO ()
sendNotification lf s =
  LSP.sendFunc lf $
    LSP.NotLogMessage $
    LSP.NotificationMessage "2.0" LSP.WindowLogMessage $
    LSP.LogMessageParams LSP.MtInfo s

diagnosticSource :: LSP.DiagnosticSource
diagnosticSource = "sixten"

errorToDiagnostic :: (Error.Hydrated, Doc ann) -> LSP.Diagnostic
errorToDiagnostic (err, doc) = LSP.Diagnostic
  { _range = spanToRange $ Error.Hydrated._lineColumn err
  , _severity = Just LSP.DsError
  , _code = Nothing
  , _source = Just diagnosticSource
  , _message = show doc
  , _relatedInformation = Nothing
  }

spanToRange :: Span.LineColumn -> LSP.Range
spanToRange (Span.LineColumns start end) =
  LSP.Range
    { _start = positionToPosition start
    , _end = positionToPosition end
    }

positionToPosition :: Position.LineColumn -> LSP.Position
positionToPosition (Position.LineColumn line column) =
  LSP.Position
    { _line = line
    , _character = column
    }

fileContents :: LSP.LspFuncs () -> LSP.Uri -> IO (LSP.TextDocumentVersion, Text)
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf $ LSP.toNormalizedUri uri
  case mvf of
    Just (LSP.VirtualFile version rope _) -> pure (Just version, Rope.toText rope)
    Nothing ->
      case LSP.uriToFilePath uri of
        Just fp ->
          (,) Nothing <$> Text.readFile fp

        Nothing ->
          pure (Just 0, "")

withContentsWhenUpToDate :: LSP.LspFuncs () -> LSP.Uri -> LSP.TextDocumentVersion -> (Text -> IO ()) -> IO ()
withContentsWhenUpToDate lf document version k = do
  (currentVersion, contents) <- fileContents lf document
  case (version, currentVersion) of
    (Just v, Just cv)
      | v < cv ->
        pure ()

    _ ->
      k contents
