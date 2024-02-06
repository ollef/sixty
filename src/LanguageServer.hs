{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LanguageServer where

import Colog.Core (Severity (..), WithSeverity (..), (<&))
import qualified Colog.Core as Colog
import Control.Concurrent.STM as STM
import Control.Lens
import Data.Default (def)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Driver
import qualified Error.Hydrated
import qualified Error.Hydrated as Error (Hydrated)
import qualified FileSystem
import qualified Language.LSP.Diagnostics as LSP
import qualified Language.LSP.Logging as LSP
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
import Protolude hiding (State, handle, state)
import Query (Query)
import Rock (Task)
import qualified System.Directory as Directory
import qualified System.FSNotify as FSNotify
import qualified UTF16

run :: IO Int
run = flip
  catches
  [Handler ioExcept, Handler someExcept]
  do
    messageQueue <- newTQueueIO
    diskStateVar <- newTVarIO mempty
    stopListeningVar <- newMVar mempty
    let stderrLogger :: MonadIO m => Colog.LogAction m (WithSeverity Text)
        stderrLogger = Colog.cmap show Colog.logStringStderr
        clientLogger :: (LSP.MonadLsp c m) => Colog.LogAction m (WithSeverity Text)
        clientLogger = LSP.defaultClientLogger
        dualLogger :: (LSP.MonadLsp c m) => Colog.LogAction m (WithSeverity Text)
        dualLogger = clientLogger <> stderrLogger
        serverDefinition =
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
                        stopListening <- FileSystem.runWatcher (FileSystem.projectWatcher projectFile') manager \newState -> do
                          atomically $ modifyTVar' diskStateVar \state ->
                            newState {FileSystem.changedFiles = state.changedFiles <> newState.changedFiles}

                        join $ swapMVar stopListeningVar stopListening

                driverState <- Driver.initialState
                let state =
                      State
                        { driverState
                        , diskStateVar
                        }
                _ <- forkIO $ LSP.runLspT env $ runReaderT (reactor stderrLogger $ readTQueue messageQueue) state
                pure $ Right (env, state)
            , staticHandlers = \_clientCapabilities -> lspHandlers dualLogger messageQueue
            , options
            , interpretHandler = \(env, state) -> LSP.Iso (LSP.runLspT env . flip runReaderT state) liftIO
            , configSection = "sixten"
            , parseConfig = \() _ -> Right ()
            , onConfigChange = pure
            }
    LSP.runServerWithHandles
      (Colog.cmap (fmap logToText) stderrLogger)
      (Colog.cmap (fmap logToText) dualLogger)
      stdin
      stdout
      serverDefinition
      `finally` do
        join $ swapMVar stopListeningVar mempty
  where
    logToText = Text.pack . show . Doc.pretty
    ioExcept (e :: IOException) = do
      print e
      return 1
    someExcept (e :: IOException) = do
      print e
      return 1

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

type StateM = ReaderT State (LSP.LspT () IO)

data State = State
  { driverState :: !(Driver.State (Error.Hydrated, Doc Void))
  , diskStateVar :: !(TVar FileSystem.ProjectFiles)
  }

type ReactorMessage = StateM ()

reactor :: Colog.LogAction StateM (WithSeverity Text) -> STM ReactorMessage -> StateM ()
reactor logger receiveMessage = do
  state <- ask
  forever do
    join $
      liftIO $
        atomically $
          receiveMessage
            <|> checkAllAndPublishDiagnostics logger <$ hasChangedFiles state
  where
    hasChangedFiles state = do
      diskState <- readTVar state.diskStateVar
      guard $ not $ HashSet.null diskState.changedFiles

lspHandlers :: Colog.LogAction StateM (WithSeverity Text) -> TQueue ReactorMessage -> LSP.Handlers StateM
lspHandlers logger messageQueue = LSP.mapHandlers goReq goNot $ handle logger
  where
    goReq :: forall (a :: LSP.Method LSP.ClientToServer LSP.Request). LSP.Handler StateM a -> LSP.Handler StateM a
    goReq f msg k =
      liftIO $ atomically $ writeTQueue messageQueue $ f msg k

    goNot :: forall (a :: LSP.Method LSP.ClientToServer LSP.Notification). LSP.Handler StateM a -> LSP.Handler StateM a
    goNot f msg =
      liftIO $ atomically $ writeTQueue messageQueue $ f msg

handle :: Colog.LogAction StateM (WithSeverity Text) -> LSP.Handlers StateM
handle logger =
  mconcat
    [ LSP.notificationHandler LSP.SMethod_TextDocumentDidOpen \message -> do
        state <- ask
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
        filePath <- liftIO $ Directory.canonicalizePath $ uriToFilePath uri
        liftIO $ atomically $ modifyTVar state.diskStateVar \diskState ->
          diskState {FileSystem.changedFiles = HashSet.insert filePath diskState.changedFiles}
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidChange \message -> do
        state <- ask
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
        filePath <- liftIO $ Directory.canonicalizePath $ uriToFilePath uri
        liftIO $ atomically $ modifyTVar state.diskStateVar \diskState ->
          diskState {FileSystem.changedFiles = HashSet.insert filePath diskState.changedFiles}
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidSave \message -> do
        state <- ask
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
        filePath <- liftIO $ Directory.canonicalizePath $ uriToFilePath uri
        liftIO $ atomically $ modifyTVar state.diskStateVar \diskState ->
          diskState {FileSystem.changedFiles = HashSet.insert filePath diskState.changedFiles}
    , LSP.notificationHandler LSP.SMethod_TextDocumentDidClose \message -> do
        state <- ask
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
        filePath <- liftIO $ Directory.canonicalizePath $ uriToFilePath uri
        liftIO $ atomically $ modifyTVar state.diskStateVar \diskState ->
          diskState {FileSystem.changedFiles = HashSet.insert filePath diskState.changedFiles}
    , LSP.requestHandler LSP.SMethod_TextDocumentHover \message respond -> do
        logger <& ("handle HoverRequest: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position

        (maybeAnnotation, _) <-
          runTask Driver.Don'tPrune $
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
    , LSP.requestHandler LSP.SMethod_TextDocumentDefinition \message respond -> do
        logger <& ("handle DefinitionRequest: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position

        (maybeLocation, _) <-
          runTask Driver.Don'tPrune $
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
    , LSP.requestHandler LSP.SMethod_TextDocumentCompletion \message respond -> do
        logger <& ("handle CompletionRequest: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position
            maybeContext = message ^. LSP.params . LSP.context

        (completions, _) <-
          runTask Driver.Don'tPrune $
            case maybeContext of
              Just (LSP.CompletionContext LSP.CompletionTriggerKind_TriggerCharacter (Just "?")) ->
                Completion.questionMark (uriToFilePath uri) (positionFromPosition position)
              _ ->
                Completion.complete (uriToFilePath uri) (positionFromPosition position)

        logger <& ("handle CompletionResponse: " <> show completions) `WithSeverity` Info

        let response =
              LSP.CompletionList
                { LSP._isIncomplete = False
                , LSP._itemDefaults = Nothing
                , LSP._items = fold completions
                }

        respond $ Right $ LSP.InR $ LSP.InL response
    , LSP.requestHandler LSP.SMethod_TextDocumentDocumentHighlight \message respond -> do
        logger <& ("handle DocumentHighlight: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position

        (highlights, _) <-
          runTask Driver.Don'tPrune $
            DocumentHighlights.highlights (uriToFilePath uri) (positionFromPosition position)

        let response =
              [ LSP.DocumentHighlight
                { _range = spanToRange span
                , _kind = Just LSP.DocumentHighlightKind_Read
                }
              | span <- highlights
              ]

        logger <& ("handle DocumentHighlightResponse: " <> show highlights) `WithSeverity` Info
        respond $ Right $ LSP.InL response
    , LSP.requestHandler LSP.SMethod_TextDocumentReferences \message respond -> do
        logger <& ("handle References: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position

        (references, _) <-
          runTask Driver.Don'tPrune $
            References.references (uriToFilePath uri) (positionFromPosition position)

        let response =
              [ LSP.Location
                { _uri = LSP.filePathToUri filePath
                , _range = spanToRange span
                }
              | (_item, references') <- references
              , (filePath, span) <- references'
              ]

        logger <& ("handle ReferencesResponse: " <> show response) `WithSeverity` Info
        respond $ Right $ LSP.InL response
    , LSP.requestHandler LSP.SMethod_TextDocumentRename \message respond -> do
        logger <& ("handle RenameRequest: " <> show message) `WithSeverity` Info
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri
            position = message ^. LSP.params . LSP.position
            newName = message ^. LSP.params . LSP.newName

        (references, _) <-
          runTask Driver.Don'tPrune $
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

        logger <& ("handle RenameResponse: " <> show references) `WithSeverity` Info
        respond $ Right $ LSP.InL response
    , LSP.requestHandler LSP.SMethod_TextDocumentCodeLens \message respond -> do
        let document = message ^. LSP.params . LSP.textDocument
            uri = document ^. LSP.uri

        (codeLenses, _) <-
          runTask Driver.Don'tPrune $
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
    ]

-------------------------------------------------------------------------------

checkAllAndPublishDiagnostics :: Colog.LogAction StateM (WithSeverity Text) -> StateM ()
checkAllAndPublishDiagnostics logger = do
  state <- ask
  diskState <- liftIO $ atomically do
    diskState <- readTVar state.diskStateVar
    writeTVar state.diskStateVar diskState {FileSystem.changedFiles = mempty}
    pure diskState
  logger <& ("checkAllAndPublishDiagnostics changed files " <> show diskState.changedFiles) `WithSeverity` Info
  vfs <- LSP.getVirtualFiles
  let allFiles =
        fmap mempty (HashMap.fromList $ fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap mempty diskState.fileContents
  (_, errors) <- runTask Driver.Prune Driver.checkAll
  let errorsByFilePath =
        HashMap.fromListWith
          (<>)
          [ (error.filePath, [errorToDiagnostic error errorDoc])
          | (error, errorDoc) <- errors
          ]
          <> allFiles

  forM_ (HashMap.toList errorsByFilePath) \(filePath, diagnostics) -> do
    let uri = LSP.filePathToUri filePath
    versionedDoc <- LSP.getVersionedTextDoc $ LSP.TextDocumentIdentifier uri

    publishDiagnostics (LSP.toNormalizedUri uri) (versionedDoc ^. LSP.version) diagnostics

runTask
  :: Driver.Prune
  -> Task Query a
  -> StateM (a, [(Error.Hydrated, Doc Void)])
runTask prune task = do
  state <- ask
  diskState <- liftIO $ atomically do
    diskState <- readTVar state.diskStateVar
    writeTVar state.diskStateVar diskState {FileSystem.changedFiles = mempty}
    pure diskState
  vfs <- LSP.getVirtualFiles
  let prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
      prettyError err = do
        (heading, body) <- Error.Hydrated.headingAndBody err.error
        pure (err, heading <> Doc.line <> body)

      files =
        HashMap.fromList (fmap (bimap (uriToFilePath . LSP.fromNormalizedUri) (Left . view LSP.file_text)) $ Map.toList $ vfs ^. LSP.vfsMap) <> fmap Right diskState.fileContents

  liftIO $
    Driver.runIncrementalTask
      state.driverState
      diskState.changedFiles
      (HashSet.fromList diskState.sourceDirectories)
      files
      prettyError
      prune
      task

-------------------------------------------------------------------------------

type TextDocumentVersion = Int32

publishDiagnostics :: LSP.NormalizedUri -> TextDocumentVersion -> [LSP.Diagnostic] -> StateM ()
publishDiagnostics uri version diagnostics =
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
