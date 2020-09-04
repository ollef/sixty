{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LanguageServer where

import Protolude hiding (State, state)

import Control.Concurrent.STM as STM
import Control.Lens
import Data.Default (def)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Rope.UTF16 (Rope)
import qualified Data.Rope.UTF16 as Rope
import Data.Text.Prettyprint.Doc (Doc)
import qualified Data.Text.Prettyprint.Doc as Doc
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.Messages as LSP
import qualified Language.Haskell.LSP.Types as LSP
import qualified Language.Haskell.LSP.Types.Lens as LSP hiding (rootPath)
import qualified Language.Haskell.LSP.VFS as LSP
import Rock (Task)
import qualified System.Directory as Directory
import qualified System.FSNotify as FSNotify

import qualified Driver
import qualified Error.Hydrated as Error (Hydrated)
import qualified Error.Hydrated
import qualified FileSystem
import qualified LanguageServer.Completion as Completion
import qualified LanguageServer.CodeLens as CodeLens
import qualified LanguageServer.DocumentHighlights as DocumentHighlights
import qualified LanguageServer.GoToDefinition as GoToDefinition
import qualified LanguageServer.Hover as Hover
import qualified LanguageServer.References as References
import qualified Occurrences.Intervals
import qualified Position
import qualified Project
import Query (Query)
import qualified Span

run :: IO ()
run = do
  messageQueue <- newTQueueIO
  signalChangeVar <- newEmptyTMVarIO
  diskFileStateVar <- newMVar mempty
  stopListeningVar <- newMVar mempty
  _ <- LSP.run
    LSP.InitializeCallbacks
      { LSP.onInitialConfiguration = \_ -> Right ()
      , LSP.onConfigurationChange = \_ -> Right ()
      , LSP.onStartup = \lf -> do
        case LSP.rootPath lf of
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
        _ <- forkIO $ messagePump State
          { _lspFuncs = lf
          , _driverState = driverState
          , _receiveMessage = readTQueue messageQueue
          , _diskChangeSignalled = takeTMVar signalChangeVar
          , _diskFileStateVar = diskFileStateVar
          , _sourceDirectories = mempty
          , _diskFiles = mempty
          , _openFiles = mempty
          , _changedFiles = mempty
          }

        pure Nothing
      }
    (handlers $ atomically . writeTQueue messageQueue)
    options
    Nothing -- (Just "sixten-lsp.log")
    `finally` do
      join $ swapMVar stopListeningVar mempty

  pure ()
  where
    config =
      FSNotify.defaultConfig
        { FSNotify.confDebounce = FSNotify.Debounce 0.010
        }

handlers :: (LSP.FromClientMessage -> IO ()) -> LSP.Handlers
handlers sendMessage =
  def
    { LSP.initializedHandler = Just $ sendMessage . LSP.NotInitialized
    , LSP.didOpenTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidOpenTextDocument
    , LSP.didChangeTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidChangeTextDocument
    , LSP.didCloseTextDocumentNotificationHandler = Just $ sendMessage . LSP.NotDidCloseTextDocument
    , LSP.hoverHandler = Just $ sendMessage . LSP.ReqHover
    , LSP.definitionHandler = Just $ sendMessage . LSP.ReqDefinition
    , LSP.completionHandler = Just $ sendMessage . LSP.ReqCompletion
    , LSP.documentHighlightHandler = Just $ sendMessage . LSP.ReqDocumentHighlights
    , LSP.referencesHandler = Just $ sendMessage . LSP.ReqFindReferences
    , LSP.renameHandler = Just $ sendMessage . LSP.ReqRename
    , LSP.codeLensHandler = Just $ sendMessage . LSP.ReqCodeLens
    }

options :: LSP.Options
options = def
  { Language.Haskell.LSP.Core.textDocumentSync = Just LSP.TextDocumentSyncOptions
    { LSP._openClose = Just True
    , LSP._change = Just LSP.TdSyncIncremental
    , LSP._willSave = Just False
    , LSP._willSaveWaitUntil = Just False
    , LSP._save = Just $ LSP.SaveOptions $ Just False
    }
  , LSP.completionTriggerCharacters = Just "?"
  }

data State = State
  { _lspFuncs :: !(LSP.LspFuncs ())
  , _driverState :: !(Driver.State (Error.Hydrated, Doc Void))
  , _receiveMessage :: !(STM LSP.FromClientMessage)
  , _diskChangeSignalled :: !(STM ())
  , _diskFileStateVar :: !(MVar (HashSet FilePath, [FileSystem.Directory], HashMap FilePath Text))
  , _sourceDirectories :: [FileSystem.Directory]
  , _diskFiles :: HashMap FilePath Text
  , _openFiles :: HashMap FilePath Rope
  , _changedFiles :: HashSet FilePath
  }

messagePump :: State -> IO ()
messagePump state = do
  sendNotification state $ "messagePump changed files: " <> show (_changedFiles state)
  join $ atomically $
    onMessage <$> _receiveMessage state <|>
    onDiskChange <$ _diskChangeSignalled state <|>
    onOutOfDate <$ guard (not $ HashSet.null $ _changedFiles state)
  where
    onDiskChange = do
      (changedFiles, sourceDirectories, diskFiles) <- modifyMVar (_diskFileStateVar state) $ \(changedFiles, sourceDirectories, diskFiles) ->
        pure ((mempty, sourceDirectories, diskFiles), (changedFiles, sourceDirectories, diskFiles))
      messagePump state
        { _sourceDirectories = sourceDirectories
        , _diskFiles = diskFiles
        , _changedFiles = changedFiles <> _changedFiles state
        }

    onOutOfDate = do
      checkAllAndPublishDiagnostics state
      messagePump state
        { _changedFiles = mempty
        }

    onMessage message =
      case message of
        LSP.NotInitialized _ ->
          messagePump state

        LSP.NotDidOpenTextDocument notification -> do
          let
            document =
              notification ^. LSP.params . LSP.textDocument

            uri =
              document ^. LSP.uri

            text =
              document ^. LSP.text

          filePath <- Directory.canonicalizePath $ uriToFilePath uri

          messagePump state
            { _openFiles = HashMap.insert filePath (Rope.fromText text) (_openFiles state)
            , _changedFiles = HashSet.insert filePath (_changedFiles state)
            }

        LSP.NotDidChangeTextDocument notification -> do
          let
            uri =
              notification ^. LSP.params . LSP.textDocument . LSP.uri

          filePath <- Directory.canonicalizePath $ uriToFilePath uri

          messagePump state
            { _openFiles =
              HashMap.adjust
                (flip LSP.applyChanges $ toList $ notification ^. LSP.params . LSP.contentChanges)
                filePath
                (_openFiles state)
            , _changedFiles = HashSet.insert filePath (_changedFiles state)
            }

        LSP.NotDidCloseTextDocument notification -> do
          let
            document =
              notification ^. LSP.params . LSP.textDocument

            uri =
              document ^. LSP.uri

          filePath <- Directory.canonicalizePath $ uriToFilePath uri

          messagePump state
            { _openFiles = HashMap.delete filePath $ _openFiles state
            , _changedFiles = HashSet.insert filePath $ _changedFiles state
            }

        LSP.ReqHover req -> do
          sendNotification state $ "messagePump: HoverRequest: " <> show req
          let
            LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) position _ =
              req ^. LSP.params

          (maybeAnnotation, _) <- runTask state Driver.Don'tPrune $
            Hover.hover (uriToFilePath uri) (positionFromPosition position)

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

          LSP.sendFunc (_lspFuncs state) $ LSP.RspHover $ LSP.makeResponseMessage req response
          messagePump state

        LSP.ReqDefinition req -> do
          sendNotification state $ "messagePump: DefinitionRequest: " <> show req
          let
            LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) position _ =
              req ^. LSP.params

          (maybeLocation, _) <- runTask state Driver.Don'tPrune $
            GoToDefinition.goToDefinition (uriToFilePath uri) (positionFromPosition position)

          case maybeLocation of
            Nothing ->
              LSP.sendErrorResponseS
                (LSP.sendFunc $ _lspFuncs state)
                (LSP.responseId $ req ^. LSP.id)
                LSP.UnknownErrorCode
                "Couldn't find a definition to jump to under the cursor"

            Just (file, span) ->
              LSP.sendFunc (_lspFuncs state) $
                LSP.RspDefinition $
                LSP.makeResponseMessage req $
                LSP.SingleLoc $
                spanToLocation file span
          messagePump state

        LSP.ReqCompletion req -> do
          sendNotification state $ "messagePump: CompletionRequest: " <> show req
          let
            LSP.CompletionParams (LSP.TextDocumentIdentifier uri) position maybeContext _ =
              req ^. LSP.params

          (completions, _) <-
            runTask state Driver.Don'tPrune $
              case maybeContext of
                Just (LSP.CompletionContext LSP.CtTriggerCharacter (Just "?")) ->
                  Completion.questionMark (uriToFilePath uri) (positionFromPosition position)

                _ ->
                  Completion.complete (uriToFilePath uri) (positionFromPosition position)

          sendNotification state $ "messagePump: CompletionResponse: " <> show completions

          let
            response =
              LSP.CompletionList LSP.CompletionListType
                { LSP._isIncomplete = False
                , LSP._items = LSP.List $ fold completions
                }

          LSP.sendFunc (_lspFuncs state) $ LSP.RspCompletion $ LSP.makeResponseMessage req response
          messagePump state

        LSP.ReqDocumentHighlights req -> do
          sendNotification state $ "messagePump: document highlights request: " <> show req
          let
            LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) position _ =
              req ^. LSP.params


          (highlights, _) <- runTask state Driver.Don'tPrune $
            DocumentHighlights.highlights (uriToFilePath uri) (positionFromPosition position)

          let
            response =
              LSP.List
                [ LSP.DocumentHighlight
                  { _range = spanToRange span
                  , _kind = Just LSP.HkRead
                  }
                | span <- highlights
                ]

          sendNotification state $ "messagePump: document highlights response: " <> show highlights
          LSP.sendFunc (_lspFuncs state) $ LSP.RspDocumentHighlights $ LSP.makeResponseMessage req response
          messagePump state

        LSP.ReqFindReferences req -> do
          sendNotification state $ "messagePump: references request: " <> show req
          let
            -- TODO use context
            LSP.ReferenceParams (LSP.TextDocumentIdentifier uri) position _context _ =
              req ^. LSP.params


          (references, _) <- runTask state Driver.Don'tPrune $
            References.references (uriToFilePath uri) (positionFromPosition position)

          let
            response =
              LSP.List
                [ LSP.Location
                  { _uri = LSP.filePathToUri filePath
                  , _range = spanToRange span
                  }
                | (_item, references') <- references
                , (filePath, span) <- references'
                ]

          sendNotification state $ "messagePump: references response: " <> show response
          LSP.sendFunc (_lspFuncs state) $ LSP.RspFindReferences $ LSP.makeResponseMessage req response
          messagePump state

        LSP.ReqRename req -> do
          sendNotification state $ "messagePump: rename request: " <> show req
          let
            LSP.RenameParams (LSP.TextDocumentIdentifier uri) position newName _ =
              req ^. LSP.params

          (references, _) <- runTask state Driver.Don'tPrune $
            References.references (uriToFilePath uri) (positionFromPosition position)

          let
            response =
              LSP.WorkspaceEdit
                { _changes = Just $
                  HashMap.fromListWith (<>)
                  [ ( LSP.filePathToUri filePath
                    , LSP.List
                      [LSP.TextEdit
                        { _range = spanToRange $ Occurrences.Intervals.nameSpan item span
                        , _newText  = newName
                        }
                      ]
                    )
                  | (item, references') <- references
                  , (filePath, span) <- references'
                  ]
                , _documentChanges = Nothing
                }


          sendNotification state $ "messagePump: rename response: " <> show references
          LSP.sendFunc (_lspFuncs state) $ LSP.RspRename $ LSP.makeResponseMessage req response
          messagePump state

        LSP.ReqCodeLens req -> do
          let
            LSP.CodeLensParams (LSP.TextDocumentIdentifier uri) _ =
              req ^. LSP.params

          (codeLenses, _) <- runTask state Driver.Don'tPrune $
            CodeLens.codeLens $ uriToFilePath uri
          let
            response =
              LSP.List
                [ LSP.CodeLens
                  { _range = spanToRange span
                  , _command = Just LSP.Command
                    { _title = show doc
                    , _command = ""
                    , _arguments = Nothing
                    }
                  , _xdata = Nothing
                  }
                | (span, doc) <- codeLenses
                ]
          LSP.sendFunc (_lspFuncs state) $ LSP.RspCodeLens $ LSP.makeResponseMessage req response
          messagePump state
        _ ->
          messagePump state

-------------------------------------------------------------------------------

checkAllAndPublishDiagnostics :: State -> IO ()
checkAllAndPublishDiagnostics state = do
  let
    allFiles =
      fmap mempty (_openFiles state) <> fmap mempty (_diskFiles state)
  (_, errors) <- runTask state Driver.Prune Driver.checkAll
  let
    errorsByFilePath =
      HashMap.fromListWith (<>)
        [ (Error.Hydrated._filePath error, [errorToDiagnostic error errorDoc])
        | (error, errorDoc) <- errors
        ]
      <> allFiles

  forM_ (HashMap.toList errorsByFilePath) $ \(filePath, diagnostics) ->
    publishDiagnostics state (LSP.filePathToUri filePath) diagnostics

runTask
  :: forall a
  . State
  -> Driver.Prune
  -> Task Query a
  -> IO (a, [(Error.Hydrated, Doc Void)])
runTask state prune task = do
  let
    prettyError :: Error.Hydrated -> Task Query (Error.Hydrated, Doc ann)
    prettyError err = do
      (heading, body) <- Error.Hydrated.headingAndBody $ Error.Hydrated._error err
      pure (err, heading <> Doc.line <> body)

    files =
      fmap Rope.toText (_openFiles state) <> _diskFiles state

  Driver.runIncrementalTask
    (_driverState state)
    (_changedFiles state)
    (_sourceDirectories state)
    files
    prettyError
    prune
    task

-------------------------------------------------------------------------------

sendNotification :: State -> Text -> IO ()
sendNotification state s =
  LSP.sendFunc (_lspFuncs state) $
    LSP.NotLogMessage $
    LSP.NotificationMessage "2.0" LSP.WindowLogMessage $
    LSP.LogMessageParams LSP.MtInfo s

publishDiagnostics :: State -> LSP.Uri -> [LSP.Diagnostic] -> IO ()
publishDiagnostics state uri diagnostics =
  LSP.sendFunc (_lspFuncs state) $
    LSP.NotPublishDiagnostics $
    LSP.NotificationMessage "2.0" LSP.TextDocumentPublishDiagnostics $
    LSP.PublishDiagnosticsParams uri (LSP.List diagnostics)

diagnosticSource :: LSP.DiagnosticSource
diagnosticSource = "sixten"

errorToDiagnostic :: Error.Hydrated -> Doc ann -> LSP.Diagnostic
errorToDiagnostic err doc = LSP.Diagnostic
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
    { _line = line
    , _character = column
    }

positionFromPosition :: LSP.Position -> Position.LineColumn
positionFromPosition (LSP.Position line column) =
  Position.LineColumn line column

uriToFilePath :: LSP.Uri -> FilePath
uriToFilePath =
  fromMaybe "<TODO no filepath>" . LSP.uriToFilePath
