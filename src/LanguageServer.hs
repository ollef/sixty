{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
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
import Data.Text.Utf16.Rope (Rope)
import qualified Data.Text.Utf16.Rope as Rope
import qualified Driver
import qualified Error.Hydrated
import qualified Error.Hydrated as Error (Hydrated)
import qualified FileSystem
import qualified Language.LSP.Diagnostics as LSP
import qualified Language.LSP.Server as LSP
import qualified Language.LSP.Server as LSP.Server
import qualified Language.LSP.Types as LSP
import qualified Language.LSP.Types.Lens as LSP hiding (rootPath)
import qualified Language.LSP.VFS as LSP
import qualified LanguageServer.CodeLens as CodeLens
import qualified LanguageServer.Completion as Completion
import qualified LanguageServer.DocumentHighlights as DocumentHighlights
import qualified LanguageServer.GoToDefinition as GoToDefinition
import qualified LanguageServer.Hover as Hover
import qualified LanguageServer.References as References
import qualified Occurrences.Intervals
import qualified Position
import Prettyprinter (Doc)
import qualified Prettyprinter as Doc
import qualified Project
import Protolude hiding (State, state)
import Query (Query)
import Rock (Task)
import qualified Span
import qualified System.Directory as Directory
import qualified System.FSNotify as FSNotify

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
        , LSP.onConfigurationChange = \_ _ -> Right ()
        , LSP.doInitialize = \env _req -> do
            case LSP.resRootPath env of
              Nothing -> pure ()
              Just rootPath -> do
                maybeProjectFile <- Project.findProjectFile rootPath
                forM_ maybeProjectFile $ \projectFile -> do
                  projectFile' <- Directory.canonicalizePath projectFile
                  FSNotify.withManagerConf config $ \manager -> do
                    stopListening <- FileSystem.runWatcher (FileSystem.projectWatcher projectFile') manager $ \(changedFiles, sourceDirectories, diskFiles) -> do
                      modifyMVar_ diskFileStateVar $ \(changedFiles', _, _) ->
                        pure (changedFiles <> changedFiles', sourceDirectories, diskFiles)
                      void $ atomically $ tryPutTMVar signalChangeVar ()

                    join $ swapMVar stopListeningVar stopListening

            driverState <- Driver.initialState
            let state =
                  State
                    { _env = env
                    , _driverState = driverState
                    , _receiveMessage = readTQueue messageQueue
                    , _diskChangeSignalled = takeTMVar signalChangeVar
                    , _diskFileStateVar = diskFileStateVar
                    , _sourceDirectories = mempty
                    , _diskFiles = mempty
                    , _changedFiles = mempty
                    }
            _ <- forkIO $ messagePump state
            pure $ Right ()
        , staticHandlers = handlers $ atomically . writeTQueue messageQueue
        , options
        , interpretHandler = \() -> LSP.Iso identity identity
        }
      `finally` do
        join $ swapMVar stopListeningVar mempty

  pure ()
  where
    config =
      FSNotify.defaultConfig
        { FSNotify.confDebounce = FSNotify.Debounce 0.010
        }

handlers :: (ReceivedMessage -> IO ()) -> LSP.Handlers IO
handlers onReceivedMessage =
  mconcat
    [ LSP.notificationHandler LSP.STextDocumentDidOpen $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.STextDocumentDidChange $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.STextDocumentDidSave $ onReceivedMessage . ReceivedNotification
    , LSP.notificationHandler LSP.STextDocumentDidClose $ onReceivedMessage . ReceivedNotification
    , LSP.requestHandler LSP.STextDocumentHover $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentDefinition $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentCompletion $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentDocumentHighlight $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentReferences $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentRename $ \req -> onReceivedMessage . ReceivedRequest req
    , LSP.requestHandler LSP.STextDocumentCodeLens $ \req -> onReceivedMessage . ReceivedRequest req
    ]

options :: LSP.Options
options =
  def
    { LSP.Server.textDocumentSync =
        Just
          LSP.TextDocumentSyncOptions
            { LSP._openClose = Just True
            , LSP._change = Just LSP.TdSyncIncremental
            , LSP._willSave = Just False
            , LSP._willSaveWaitUntil = Just False
            , LSP._save = Just $ LSP.InR $ LSP.SaveOptions {_includeText = Just False}
            }
    , LSP.completionTriggerCharacters = Just "?"
    }

data ReceivedMessage where
  ReceivedRequest :: LSP.RequestMessage m -> (Either LSP.ResponseError (LSP.ResponseResult m) -> IO ()) -> ReceivedMessage
  ReceivedNotification :: LSP.NotificationMessage m -> ReceivedMessage

data State = State
  { _env :: !(LSP.LanguageContextEnv ())
  , _driverState :: !(Driver.State (Error.Hydrated, Doc Void))
  , _receiveMessage :: !(STM ReceivedMessage)
  , _diskChangeSignalled :: !(STM ())
  , _diskFileStateVar :: !(MVar (HashSet FilePath, [FileSystem.Directory], HashMap FilePath Text))
  , _sourceDirectories :: [FileSystem.Directory]
  , _diskFiles :: HashMap FilePath Text
  , _changedFiles :: HashSet FilePath
  }

messagePump :: State -> IO ()
messagePump state = do
  sendNotification state $ "messagePump changed files: " <> show (_changedFiles state)
  join $
    atomically $
      onMessage messagePump <$> _receiveMessage state
        <|> onDiskChange <$ _diskChangeSignalled state
        <|> onOutOfDate <$ guard (not $ HashSet.null $ _changedFiles state)
  where
    onDiskChange = do
      (changedFiles, sourceDirectories, diskFiles) <- modifyMVar (_diskFileStateVar state) $ \(changedFiles, sourceDirectories, diskFiles) ->
        pure ((mempty, sourceDirectories, diskFiles), (changedFiles, sourceDirectories, diskFiles))
      messagePump
        state
          { _sourceDirectories = sourceDirectories
          , _diskFiles = diskFiles
          , _changedFiles = changedFiles <> _changedFiles state
          }

    onOutOfDate = do
      checkAllAndPublishDiagnostics state
      messagePump
        state
          { _changedFiles = mempty
          }

    onMessage :: (State -> IO k) -> ReceivedMessage -> IO k
    onMessage k (ReceivedNotification message) =
      case message ^. LSP.method of
        LSP.STextDocumentDidOpen -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { _changedFiles = HashSet.insert filePath (_changedFiles state)
              }
        LSP.STextDocumentDidChange -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { _changedFiles = HashSet.insert filePath (_changedFiles state)
              }
        LSP.STextDocumentDidSave -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { _changedFiles = HashSet.insert filePath (_changedFiles state)
              }
        LSP.STextDocumentDidClose -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
          filePath <- Directory.canonicalizePath $ uriToFilePath uri
          k
            state
              { _changedFiles = HashSet.insert filePath $ _changedFiles state
              }
        _ ->
          k state
    onMessage k (ReceivedRequest message respond) =
      case message ^. LSP.method of
        LSP.STextDocumentHover -> do
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
                          LSP.HoverContents
                            LSP.MarkupContent
                              { _kind = LSP.MkPlainText
                              , _value = show doc
                              }
                      , _range = Just $ spanToRange span
                      }

          respond $ Right response
          k state
        LSP.STextDocumentDefinition -> do
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
                  LSP.ResponseError {_code = LSP.UnknownErrorCode, _message = "Couldn't find a definition to jump to under the cursor", _xdata = Nothing}
            Just (file, span) ->
              respond $ Right $ LSP.InL $ spanToLocation file span
          k state
        LSP.STextDocumentCompletion -> do
          sendNotification state $ "messagePump: CompletionRequest: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position
              maybeContext = message ^. LSP.params . LSP.context

          (completions, _) <-
            runTask state Driver.Don'tPrune $
              case maybeContext of
                Just (LSP.CompletionContext LSP.CtTriggerCharacter (Just "?")) ->
                  Completion.questionMark (uriToFilePath uri) (positionFromPosition position)
                _ ->
                  Completion.complete (uriToFilePath uri) (positionFromPosition position)

          sendNotification state $ "messagePump: CompletionResponse: " <> show completions

          let response =
                LSP.CompletionList
                  { LSP._isIncomplete = False
                  , LSP._items = LSP.List $ fold completions
                  }

          respond $ Right $ LSP.InR response
          k state
        LSP.STextDocumentDocumentHighlight -> do
          sendNotification state $ "messagePump: document highlights request: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (highlights, _) <-
            runTask state Driver.Don'tPrune $
              DocumentHighlights.highlights (uriToFilePath uri) (positionFromPosition position)

          let response =
                LSP.List
                  [ LSP.DocumentHighlight
                    { _range = spanToRange span
                    , _kind = Just LSP.HkRead
                    }
                  | span <- highlights
                  ]

          sendNotification state $ "messagePump: document highlights response: " <> show highlights
          respond $ Right response
          k state
        LSP.STextDocumentReferences -> do
          sendNotification state $ "messagePump: references request: " <> show message
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri
              position = message ^. LSP.params . LSP.position

          (references, _) <-
            runTask state Driver.Don'tPrune $
              References.references (uriToFilePath uri) (positionFromPosition position)

          let response =
                LSP.List
                  [ LSP.Location
                    { _uri = LSP.filePathToUri filePath
                    , _range = spanToRange span
                    }
                  | (_item, references') <- references
                  , (filePath, span) <- references'
                  ]

          sendNotification state $ "messagePump: references response: " <> show response
          respond $ Right response
          k state
        LSP.STextDocumentRename -> do
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
                        HashMap.fromListWith
                          (<>)
                          [ ( LSP.filePathToUri filePath
                            , LSP.List
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
          respond $ Right response
          k state
        LSP.STextDocumentCodeLens -> do
          let document = message ^. LSP.params . LSP.textDocument
              uri = document ^. LSP.uri

          (codeLenses, _) <-
            runTask state Driver.Don'tPrune $
              CodeLens.codeLens $
                uriToFilePath uri
          let response =
                LSP.List
                  [ LSP.CodeLens
                    { _range = spanToRange span
                    , _command =
                        Just
                          LSP.Command
                            { _title = show doc
                            , _command = ""
                            , _arguments = Nothing
                            }
                    , _xdata = Nothing
                    }
                  | (span, doc) <- codeLenses
                  ]
          respond $ Right response
          k state
        _ ->
          k state

-------------------------------------------------------------------------------

checkAllAndPublishDiagnostics :: State -> IO ()
checkAllAndPublishDiagnostics state = do
  vfs <- LSP.runLspT (_env state) LSP.getVirtualFiles
  let allFiles =
        fmap mempty (HashMap.fromList $ fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap mempty (_diskFiles state)
  (_, errors) <- runTask state Driver.Prune Driver.checkAll
  let errorsByFilePath =
        HashMap.fromListWith
          (<>)
          [ (Error.Hydrated._filePath error, [errorToDiagnostic error errorDoc])
          | (error, errorDoc) <- errors
          ]
          <> allFiles

  forM_ (HashMap.toList errorsByFilePath) $ \(filePath, diagnostics) -> do
    let uri = LSP.filePathToUri filePath
    versionedDoc <- LSP.runLspT (_env state) $ LSP.getVersionedTextDoc $ LSP.TextDocumentIdentifier uri

    publishDiagnostics state (LSP.toNormalizedUri uri) (versionedDoc ^. LSP.version) diagnostics

runTask ::
  State ->
  Driver.Prune ->
  Task Query a ->
  IO (a, [(Error.Hydrated, Doc Void)])
runTask state prune task = do
  vfs <- LSP.runLspT (_env state) LSP.getVirtualFiles
  let prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
      prettyError err = do
        (heading, body) <- Error.Hydrated.headingAndBody $ Error.Hydrated._error err
        pure (err, heading <> Doc.line <> body)

      files =
        HashMap.fromList (fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (Left . view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap Right (_diskFiles state)

  Driver.runIncrementalTask
    (_driverState state)
    (_changedFiles state)
    (HashSet.fromList $ _sourceDirectories state)
    files
    prettyError
    prune
    task

-------------------------------------------------------------------------------

sendNotification :: State -> Text -> IO ()
sendNotification state s =
  LSP.runLspT
    (_env state)
    $ LSP.sendNotification
      LSP.SWindowLogMessage
      LSP.LogMessageParams {_xtype = LSP.MtInfo, _message = s}

publishDiagnostics :: State -> LSP.NormalizedUri -> LSP.TextDocumentVersion -> [LSP.Diagnostic] -> IO ()
publishDiagnostics state uri version diagnostics =
  LSP.runLspT (_env state) $
    LSP.Server.publishDiagnostics maxDiagnostics uri version (LSP.partitionBySource diagnostics)
  where
    maxDiagnostics = 100

diagnosticSource :: LSP.DiagnosticSource
diagnosticSource = "sixten"

errorToDiagnostic :: Error.Hydrated -> Doc ann -> LSP.Diagnostic
errorToDiagnostic err doc =
  LSP.Diagnostic
    { _range = spanToRange $ Error.Hydrated._lineColumn err
    , _severity = Just LSP.DsError
    , _code = Nothing
    , _source = Just diagnosticSource
    , _message = show doc
    , _relatedInformation = Nothing
    , _tags = Nothing
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
    { _line = fromIntegral line
    , _character = fromIntegral column
    }

positionFromPosition :: LSP.Position -> Position.LineColumn
positionFromPosition (LSP.Position line column) =
  Position.LineColumn (fromIntegral line) (fromIntegral column)

uriToFilePath :: LSP.Uri -> FilePath
uriToFilePath =
  fromMaybe "<TODO no filepath>" . LSP.uriToFilePath

applyChanges :: Rope -> [LSP.TextDocumentContentChangeEvent] -> Rope
applyChanges = foldl' applyChange

applyChange :: Rope -> LSP.TextDocumentContentChangeEvent -> Rope
applyChange _ (LSP.TextDocumentContentChangeEvent Nothing _ str) =
  Rope.fromText str
applyChange str (LSP.TextDocumentContentChangeEvent (Just (LSP.Range (LSP.Position sl sc) (LSP.Position fl fc))) _ txt) =
  changeChars str (Rope.Position (fromIntegral sl) (fromIntegral sc)) (Rope.Position (fromIntegral fl) (fromIntegral fc)) txt

changeChars :: Rope -> Rope.Position -> Rope.Position -> Text -> Rope
changeChars str start finish new = do
  case Rope.splitAtPosition finish str of
    Nothing -> panic "split inside code point"
    Just (before, after) -> case Rope.splitAtPosition start before of
      Nothing -> panic "split inside code point"
      Just (before', _) -> mconcat [before', Rope.fromText new, after]
