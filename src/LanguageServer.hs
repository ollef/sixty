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
import qualified Data.HashMap.Lazy as HashMap
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
import qualified LanguageServer.GoToDefinition as GoToDefinition
import qualified LanguageServer.Hover as Hover
import qualified Position
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
    , LSP.definitionHandler = Just $ sendMessage . LSP.ReqDefinition
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
          uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version
          filePath = uriToFilePath uri
        sendNotification lf $ "filePath = " <> show filePath
        checkAllAndPublishDiagnostics lf state uri (Just version)

      LSP.NotDidChangeTextDocument notification -> do
        let
          uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
          version = notification ^. LSP.params . LSP.textDocument . LSP.version

        sendNotification lf $ "messagePump:processing NotDidChangeTextDocument: uri=" <> show uri
        checkAllAndPublishDiagnostics lf state uri version

      LSP.NotDidSaveTextDocument notification -> do
        sendNotification lf "messagePump: processing NotDidSaveTextDocument"
        let
          uri = notification ^. LSP.params . LSP.textDocument . LSP.uri
          filePath = uriToFilePath uri
        sendNotification lf $ "filePath = " <> show filePath
        checkAllAndPublishDiagnostics lf state uri Nothing

      LSP.ReqHover req -> do
        sendNotification lf $ "messagePump: HoverRequest: " <> show req
        let
          LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) position =
            req ^. LSP.params

        (_, contents) <- fileContents lf uri
        (maybeAnnotation, _) <- runTask state uri contents Driver.Don'tPrune $
          Hover.hover (uriToFilePath uri) contents (positionFromPosition position)

        let
          response =
            foreach maybeAnnotation $
              \(span, doc) ->
                LSP.Hover
                  { _contents = LSP.HoverContents LSP.MarkupContent
                    { _kind = LSP.MkPlainText
                    , _value = show doc
                    }
                  , _range = Just $ spanToRange span
                  }

        LSP.sendFunc lf $ LSP.RspHover $ LSP.makeResponseMessage req response

      LSP.ReqDefinition req -> do
        sendNotification lf $ "messagePump: DefinitionRequest: " <> show req
        let
          LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) position =
            req ^. LSP.params

        (_, contents) <- fileContents lf uri

        (maybeLocation, _) <- runTask state uri contents Driver.Don'tPrune $
          GoToDefinition.goToDefinition (uriToFilePath uri) contents (positionFromPosition position)

        case maybeLocation of
          Nothing ->
            LSP.sendErrorResponseS
              (LSP.sendFunc lf)
              (LSP.responseId $ req ^. LSP.id)
              LSP.UnknownErrorCode
              "Couldn't find a definition to jump to under the cursor"

          Just (file, span) ->
            LSP.sendFunc lf $
              LSP.RspDefinition $
              LSP.makeResponseMessage req $
              LSP.SingleLoc $
              spanToLocation file span

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
checkAllAndPublishDiagnostics lf state uri version =
  withContentsWhenUpToDate lf uri version $ \contents -> do
    (_, errors) <- runTask state uri contents Driver.Prune $ Driver.checkAll [uriToFilePath uri]
    LSP.publishDiagnosticsFunc lf (length errors) (LSP.toNormalizedUri uri) version
      $ LSP.partitionBySource $ errorToDiagnostic <$> errors

runTask
  :: forall a ann
  . Driver.State (Error.Hydrated, Doc ann)
  -> LSP.Uri
  -> Text
  -> Driver.Prune
  -> Task Query a
  -> IO (a, [(Error.Hydrated, Doc ann)])
runTask state uri contents prune task = do
  let
    prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
    prettyError err = do
      (heading, body) <- Error.Hydrated.headingAndBody $ Error.Hydrated._error err
      pure (err, heading <> Doc.line <> body)

  Driver.runIncrementalTask state (HashMap.singleton (uriToFilePath uri) contents) prettyError prune task

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

spanToLocation :: FilePath -> Span.LineColumn -> LSP.Location
spanToLocation filePath span =
  LSP.Location
    { _uri = LSP.filePathToUri filePath
    , _range = spanToRange span
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

positionFromPosition :: LSP.Position -> Position.LineColumn
positionFromPosition (LSP.Position line column) =
  Position.LineColumn line column

uriToFilePath :: LSP.Uri -> FilePath
uriToFilePath =
  fromMaybe "<TODO no filepath>" . LSP.uriToFilePath

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
withContentsWhenUpToDate lf uri version k = do
  (currentVersion, contents) <- fileContents lf uri
  case (version, currentVersion) of
    (Just v, Just cv)
      | v < cv ->
        pure ()

    _ ->
      k contents
