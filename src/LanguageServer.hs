{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module LanguageServer where

import Control.Concurrent.STM as STM
import Control.Lens
import Data.Default (def)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import qualified Driver
import qualified Error.Hydrated
import qualified Error.Hydrated as Error (Hydrated)
import qualified FileSystem
import qualified Language.LSP.Diagnostics as LSP
import qualified Language.LSP.Protocol.Lens as LSP hiding (rootPath)
import qualified Language.LSP.Protocol.Message as LSP
import qualified Language.LSP.Protocol.Types as LSP
import qualified Language.LSP.Server as LSP
import qualified Language.LSP.Server as LSP.Server
import qualified Language.LSP.VFS as LSP
import qualified LanguageServer.CodeLens as CodeLens
import qualified LanguageServer.Completion as Completion
import qualified LanguageServer.DocumentHighlights as DocumentHighlights
import qualified LanguageServer.GoToDefinition as GoToDefinition
import qualified LanguageServer.Hover as Hover
import qualified LanguageServer.References as References
import qualified Occurrences.Intervals
import Prettyprinter (Doc)
import qualified Prettyprinter as Doc
import qualified Project
import Protolude hiding (State, state)
import Query (Query)
import Rock (Task)
import qualified System.Directory as Directory
import qualified System.FSNotify as FSNotify
import qualified UTF16

run :: IO ()
run = do
  messageQueue <- newTQueueIO
  signalChangeVar <- newEmptyTMVarIO
  diskFileStateVar <- newMVar mempty
  stopListeningVar <- newMVar mempty
  _ <-
    LSP.runServer
      LSP.ServerDefinition
        { LSP.defaultConfig = ()
        , LSP.doInitialize = \env _req -> do
            case LSP.resRootPath env of
              Nothing -> pure ()
              Just rootPath -> do
                maybeProjectFile <- Project.findProjectFile rootPath
                forM_ maybeProjectFile \projectFile -> do
                  projectFile' <- Directory.canonicalizePath projectFile
                  FSNotify.withManager \manager -> do
                    stopListening <- FileSystem.runWatcher (FileSystem.projectWatcher projectFile') manager \(changedFiles, sourceDirectories, diskFiles) -> do
                      modifyMVar_ diskFileStateVar \(changedFiles', _, _) ->
                        pure (changedFiles <> changedFiles', sourceDirectories, diskFiles)
                      void $ atomically $ tryPutTMVar signalChangeVar ()

                    join $ swapMVar stopListeningVar stopListening

            driverState <- Driver.initialState
            let state =
                  State
                    { env
                    , driverState
                    , receiveMessage = readTQueue messageQueue
                    , diskChangeSignalled = takeTMVar signalChangeVar
                    , diskFileStateVar
                    , sourceDirectories = mempty
                    , diskFiles = mempty
                    , changedFiles = mempty
                    }
            _ <- forkIO $ messagePump state
            pure $ Right ()
        , staticHandlers = \_clientCapabilities -> handlers $ atomically . writeTQueue messageQueue
        , options
        , interpretHandler = \() -> LSP.Iso identity identity
        , configSection = "sixten"
        , parseConfig = \() _ -> Right ()
        , onConfigChange = pure
        }
      `finally` do
        join $ swapMVar stopListeningVar mempty

  pure ()

handlers :: (ReceivedMessage -> IO ()) -> LSP.Handlers IO
handlers onReceivedMessage =
  mconcat
    [ LSP.notificationHandler LSP.SMethod_TextDocumentDidOpen $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidChange $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidSave $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidClose $ onReceivedMessage . ReceivedNotification
    , LSP.requestHandler LSP.SMethod_TextDocumentHover \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentDefinition \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentCompletion \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentDocumentHighlight \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentReferences \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentRename \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.SMethod_TextDocumentCodeLens \req -> onReceivedMessage . ReceivedRequest req
    ]

options :: LSP.Options
options =
  def
    { LSP.Server.optTextDocumentSync =
        Just
          LSP.TextDocumentSyncOptions
            { LSP._openClose = Just True
            , LSP._change = Just LSP.TextDocumentSyncKind_Incremental
            , LSP._willSave = Just False
            , LSP._willSaveWaitUntil = Just False
            , LSP._save = Just $ LSP.InR $ LSP.SaveOptions {_includeText = Just False}
            }
    , LSP.optCompletionTriggerCharacters = Just "?"
    }

data ReceivedMessage where
  ReceivedRequest :: LSP.TRequestMessage m -> (Either LSP.ResponseError (LSP.MessageResult m) -> IO ()) -> ReceivedMessage
  ReceivedNotification :: LSP.TNotificationMessage m -> ReceivedMessage

data State = State
  { env :: !(LSP.LanguageContextEnv ())
  , driverState :: !(Driver.State (Error.Hydrated, Doc Void))
  , receiveMessage :: !(STM ReceivedMessage)
  , diskChangeSignalled :: !(STM ())
  , diskFileStateVar :: !(MVar (HashSet FilePath, [FileSystem.Directory], HashMap FilePath Text))
  , sourceDirectories :: [FileSystem.Directory]
  , diskFiles :: HashMap FilePath Text
  , changedFiles :: HashSet FilePath
  }

messagePump :: State -> IO ()
messagePump state = do
  sendNotification state $ "messagePump changed files: " <> show state.changedFiles
  join $
    atomically $
      onMessage messagePump <$> state.receiveMessage
        <|> onDiskChange <$ state.diskChangeSignalled
        <|> onOutOfDate <$ guard (not $ HashSet.null state.changedFiles)
  where
    onDiskChange = do
      (changedFiles, sourceDirectories, diskFiles) <- modifyMVar state.diskFileStateVar \(changedFiles, sourceDirectories, diskFiles) ->
        pure ((mempty, sourceDirectories, diskFiles), (changedFiles, sourceDirectories, diskFiles))
      messagePump
        state
          { sourceDirectories = sourceDirectories
          , diskFiles = diskFiles
          , changedFiles = changedFiles <> state.changedFiles
          }

    onOutOfDate = do
      checkAllAndPublishDiagnostics state
      messagePump
        state
          { changedFiles = mempty
          }

    onMessage :: (State -> IO k) -> ReceivedMessage -> IO k
    onMessage k (ReceivedNotification message) =
      case message ^. LSP.method of
        LSP.SMethod_TextDocumentDidOpen -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { changedFiles = HashSet.insert filePath state.changedFiles
              }
        LSP.SMethod_TextDocumentDidChange -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { changedFiles = HashSet.insert filePath state.changedFiles
              }
        LSP.SMethod_TextDocumentDidSave -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { changedFiles = HashSet.insert filePath state.changedFiles
              }
        LSP.SMethod_TextDocumentDidClose -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { changedFiles = HashSet.insert filePath state.changedFiles
              }
        _ ->
          k state
    onMessage k (ReceivedRequest message respond) =
      case message ^. LSP.method of
        LSP.SMethod_TextDocumentHover -> do
          sendNotification state $ "messagePump: HoverRequest: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (maybeAnnotation, _) <-
            runTask state Driver.Don'tPrune $
              Hover.hover (uriToFilePath uri) (positionFromPosition position)

          let response =
                foreach maybeAnnotation $
                  \(span, doc) ->
                    LSP.Hover
                      { _contents =
                          LSP.InL
                            LSP.MarkupContent
                              { _kind = LSP.MarkupKind_PlainText
                              , _value = show doc
                              }
                      , _range = Just $ spanToRange span
                      }

          respond $ Right $ LSP.maybeToNull response
          k state
        LSP.SMethod_TextDocumentDefinition -> do
          sendNotification state $ "messagePump: DefinitionRequest: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (maybeLocation, _) <-
            runTask state Driver.Don'tPrune $
              GoToDefinition.goToDefinition (uriToFilePath uri) (positionFromPosition position)

          case maybeLocation of
            Nothing ->
              respond $
                Left
                  LSP.ResponseError
                    { _code = LSP.InR LSP.ErrorCodes_UnknownErrorCode
                    , _message = "Couldn't find a definition to jump to under the cursor"
                    , _xdata = Nothing
                    }
            Just (file, span) ->
              respond $ Right $ LSP.InL $ LSP.Definition $ LSP.InL $ spanToLocation file span
          k state
        LSP.SMethod_TextDocumentCompletion -> do
          sendNotification state $ "messagePump: CompletionRequest: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position
              maybeContext = message ^. LSP.params . LSP.context

          (completions, _) <-
            runTask state Driver.Don'tPrune $
              case maybeContext of
                Just (LSP.CompletionContext LSP.CompletionTriggerKind_TriggerCharacter (Just "?")) ->
                  Completion.questionMark (uriToFilePath uri) (positionFromPosition position)
                _ ->
                  Completion.complete (uriToFilePath uri) (positionFromPosition position)

          sendNotification state $ "messagePump: CompletionResponse: " <> show completions

          let response =
                LSP.CompletionList
                  { LSP._isIncomplete = False
                  , LSP._itemDefaults = Nothing
                  , LSP._items = fold completions
                  }

          respond $ Right $ LSP.InR $ LSP.InL response
          k state
        LSP.SMethod_TextDocumentDocumentHighlight -> do
          sendNotification state $ "messagePump: document highlights request: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (highlights, _) <-
            runTask state Driver.Don'tPrune $
              DocumentHighlights.highlights (uriToFilePath uri) (positionFromPosition position)

          let response =
                [ LSP.DocumentHighlight
                  { _range = spanToRange span
                  , _kind = Just LSP.DocumentHighlightKind_Read
                  }
                | span <- highlights
                ]

          sendNotification state $ "messagePump: document highlights response: " <> show highlights
          respond $ Right $ LSP.InL response
          k state
        LSP.SMethod_TextDocumentReferences -> do
          sendNotification state $ "messagePump: references request: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (references, _) <-
            runTask state Driver.Don'tPrune $
              References.references (uriToFilePath uri) (positionFromPosition position)

          let response =
                [ LSP.Location
                  { _uri = LSP.filePathToUri filePath
                  , _range = spanToRange span
                  }
                | (_item, references') <- references
                , (filePath, span) <- references'
                ]

          sendNotification state $ "messagePump: references response: " <> show response
          respond $ Right $ LSP.InL response
          k state
        LSP.SMethod_TextDocumentRename -> do
          sendNotification state $ "messagePump: rename request: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position
              newName = message ^. LSP.params . LSP.newName

          (references, _) <-
            runTask state Driver.Don'tPrune $
              References.references (uriToFilePath uri) (positionFromPosition position)

          let response =
                LSP.WorkspaceEdit
                  { _changes =
                      Just $
                        Map.fromListWith
                          (<>)
                          [ ( LSP.filePathToUri filePath
                            ,
                              [ LSP.TextEdit
                                  { _range = spanToRange $ Occurrences.Intervals.nameSpan item span
                                  , _newText = newName
                                  }
                              ]
                            )
                          | (item, references') <- references
                          , (filePath, span) <- references'
                          ]
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

          sendNotification state $ "messagePump: rename response: " <> show references
          respond $ Right $ LSP.InL response
          k state
        LSP.SMethod_TextDocumentCodeLens -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri

          (codeLenses, _) <-
            runTask state Driver.Don'tPrune $
              CodeLens.codeLens $
                uriToFilePath uri
          let response =
                [ LSP.CodeLens
                  { _range = spanToRange span
                  , _command =
                      Just
                        LSP.Command
                          { _title = show doc
                          , _command = ""
                          , _arguments = Nothing
                          }
                  , _data_ = Nothing
                  }
                | (span, doc) <- codeLenses
                ]
          respond $ Right $ LSP.InL response
          k state
        _ ->
          k state

-------------------------------------------------------------------------------

checkAllAndPublishDiagnostics :: State -> IO ()
checkAllAndPublishDiagnostics state = do
  vfs <- LSP.runLspT state.env LSP.getVirtualFiles
  let allFiles =
        fmap mempty (HashMap.fromList $ fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap mempty state.diskFiles
  (_, errors) <- runTask state Driver.Prune Driver.checkAll
  let errorsByFilePath =
        HashMap.fromListWith
          (<>)
          [ (error.filePath, [errorToDiagnostic error errorDoc])
          | (error, errorDoc) <- errors
          ]
          <> allFiles

  forM_ (HashMap.toList errorsByFilePath) \(filePath, diagnostics) -> do
    let uri = LSP.filePathToUri filePath
    versionedDoc <- LSP.runLspT state.env $ LSP.getVersionedTextDoc $ LSP.TextDocumentIdentifier uri

    publishDiagnostics state (LSP.toNormalizedUri uri) (versionedDoc ^. LSP.version) diagnostics

runTask
  :: State
  -> Driver.Prune
  -> Task Query a
  -> IO (a, [(Error.Hydrated, Doc Void)])
runTask state prune task = do
  vfs <- LSP.runLspT state.env LSP.getVirtualFiles
  let prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
      prettyError err = do
        (heading, body) <- Error.Hydrated.headingAndBody err.error
        pure (err, heading <> Doc.line <> body)

      files =
        HashMap.fromList (fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (Left . view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap Right state.diskFiles

  Driver.runIncrementalTask
    state.driverState
    state.changedFiles
    (HashSet.fromList state.sourceDirectories)
    files
    prettyError
    prune
    task

-------------------------------------------------------------------------------

sendNotification :: State -> Text -> IO ()
sendNotification state s =
  LSP.runLspT
    state.env
    $ LSP.sendNotification
      LSP.SMethod_WindowLogMessage
      LSP.LogMessageParams {_type_ = LSP.MessageType_Info, _message = s}

type TextDocumentVersion = Int32

publishDiagnostics :: State -> LSP.NormalizedUri -> TextDocumentVersion -> [LSP.Diagnostic] -> IO ()
publishDiagnostics state uri version diagnostics =
  LSP.runLspT state.env $
    LSP.Server.publishDiagnostics maxDiagnostics uri (Just version) (LSP.partitionBySource diagnostics)
  where
    maxDiagnostics = 100

diagnosticSource :: Text
diagnosticSource = "sixten"

errorToDiagnostic :: Error.Hydrated -> Doc ann -> LSP.Diagnostic
errorToDiagnostic err doc =
  LSP.Diagnostic
    { _range = spanToRange err.lineColumn
    , _severity = Just LSP.DiagnosticSeverity_Error
    , _code = Nothing
    , _source = Just diagnosticSource
    , _message = show doc
    , _relatedInformation = Nothing
    , _tags = Nothing
    , _codeDescription = Nothing
    , _data_ = Nothing
    }

spanToLocation :: FilePath -> UTF16.LineColumns -> LSP.Location
spanToLocation filePath span =
  LSP.Location
    { _uri = LSP.filePathToUri filePath
    , _range = spanToRange span
    }

spanToRange :: UTF16.LineColumns -> LSP.Range
spanToRange (UTF16.LineColumns start end) =
  LSP.Range
    { _start = positionToPosition start
    , _end = positionToPosition end
    }

positionToPosition :: UTF16.LineColumn -> LSP.Position
positionToPosition (UTF16.LineColumn line column) =
  LSP.Position
    { _line = fromIntegral line
    , _character = fromIntegral $ UTF16.toInt column
    }

positionFromPosition :: LSP.Position -> UTF16.LineColumn
positionFromPosition (LSP.Position line column) =
  UTF16.LineColumn (fromIntegral line) (UTF16.CodeUnits $ fromIntegral column)

uriToFilePath :: LSP.Uri -> FilePath
uriToFilePath =
  fromMaybe "<TODO no filepath>" . LSP.uriToFilePath
