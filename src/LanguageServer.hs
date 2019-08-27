{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
module LanguageServer where

import Protolude hiding (state)

import Control.Concurrent.STM as STM
import Control.Lens
import Data.Default (def)
import qualified Data.Rope.UTF16 as Rope
import Data.Text (Text)
import qualified Data.Text.IO as Text
import Data.Text.Prettyprint.Doc (pretty)
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.Diagnostics as LSP
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import qualified Language.Haskell.LSP.Types.Lens as LSP
import qualified Language.Haskell.LSP.VFS as LSP

import qualified Driver
import qualified Error.Hydrated as Error
import qualified Position
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
        return Nothing
      }
    (handlers $ atomically . writeTQueue messageQueue)
    options
    Nothing -- (Just "sixten-lsp.log")
  return ()

handlers :: (LSP.FromClientMessage -> IO ()) -> LSP.Handlers
handlers sendMessage =
  def
    { LSP.initializedHandler = Just $ sendMessage . LSP.NotInitialized
    , LSP.didOpenTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidOpenTextDocument
    , LSP.didSaveTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidSaveTextDocument
    , LSP.didChangeTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidChangeTextDocument
    , LSP.didCloseTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidCloseTextDocument
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
        return ()

      LSP.NotDidOpenTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidOpenTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        sendDiagnostics lf state document $ Just version

      LSP.NotDidChangeTextDocument notification -> do
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version

        sendNotification lf $ "messagePump:processing NotDidChangeTextDocument: uri=" <> show document
        sendDiagnostics lf state document version

      LSP.NotDidSaveTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidSaveTextDocument"
        let
          document = notification ^. LSP.params . LSP.textDocument . LSP.uri
          fileName = LSP.uriToFilePath document
        sendNotification lf $ "fileName = " <> show fileName
        sendDiagnostics lf state document Nothing

      _ ->
        return ()

-------------------------------------------------------------------------------
sendDiagnostics
  :: LSP.LspFuncs ()
  -> Driver.State
  -> LSP.Uri
  -> LSP.TextDocumentVersion
  -> IO ()
sendDiagnostics lf state document version = do
  let
    normalizedURI =
      LSP.toNormalizedUri document
  (currentVersion, contents) <- fileContents lf normalizedURI
  case (version, currentVersion) of
    (Just v, Just cv)
      | v < cv ->
        return ()
    _ -> do
      let
        LSP.Uri uriText =
          document

        uriStr =
          toS uriText

      (_, errors) <- Driver.runIncrementalTask state uriStr contents $ Driver.checkAll [uriStr]

      LSP.publishDiagnosticsFunc lf (length errors) normalizedURI version
        $ LSP.partitionBySource $ errorToDiagnostic <$> errors

-------------------------------------------------------------------------------

sendNotification :: LSP.LspFuncs () -> Text -> IO ()
sendNotification lf s =
  LSP.sendFunc lf $
    LSP.NotLogMessage $
    LSP.NotificationMessage "2.0" LSP.WindowLogMessage $
    LSP.LogMessageParams LSP.MtInfo s

diagnosticSource :: LSP.DiagnosticSource
diagnosticSource = "sixten"

errorToDiagnostic :: Error.Hydrated -> LSP.Diagnostic
errorToDiagnostic err = LSP.Diagnostic
  { _range = spanToRange $ Error._lineColumn err
  , _severity = Just LSP.DsError
  , _code = Nothing
  , _source = Just diagnosticSource
  , _message = show $ pretty err
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

fileContents :: LSP.LspFuncs () -> LSP.NormalizedUri -> IO (LSP.TextDocumentVersion, Text)
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf uri
  case mvf of
    Just (LSP.VirtualFile version rope _) -> return (Just version, Rope.toText rope)
    Nothing ->
      case LSP.uriToFilePath (LSP.fromNormalizedUri uri) of
        Just fp ->
          (,) Nothing <$> Text.readFile fp
        Nothing ->
          return (Just 0, "")
