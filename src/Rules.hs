{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import Data.String
import Data.Text.Unsafe as Text
import Rock

import qualified Builtin
import qualified Elaboration
import qualified Environment
import Error (Error)
import qualified Error
import qualified Evaluation
import qualified Module
import Monad
import Name (Name(Name))
import qualified Name
import qualified Occurrences
import qualified Parser
import qualified Paths_sixty as Paths
import Plicity
import qualified Position
import qualified Presyntax
import Query
import qualified Query.Mapped as Mapped
import qualified Resolution
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

rules :: [FilePath] -> (FilePath -> IO Text) -> GenRules (Writer [Error] (Writer TaskKind Query)) Query
rules files readFile_ (Writer (Writer query)) =
  case query of
    InputFiles ->
      input $ do
        builtinFile <- liftIO $ Paths.getDataFileName "builtin/Builtin.vix"
        pure $ builtinFile : files

    FileText filePath ->
      input $ liftIO $ readFile_ filePath

    ModuleFile subQuery ->
      nonInput $ Mapped.errorRule ModuleFile subQuery $ do
        filePaths <- fetch InputFiles
        -- TODO check and remove duplicates
        foldM go mempty filePaths
      where
        go (modulesMap, errors) filePath = do
          (module_, _, _) <- fetch $ ParsedFile filePath
          pure
            ( HashMap.insert module_ filePath modulesMap
            , case HashMap.lookup module_ modulesMap of
              Nothing ->
                errors

              Just filePath' ->
                Error.MultipleFilesWithModuleName module_ filePath' filePath : errors
            )

    ParsedFile filePath ->
      nonInput $ do
        text <- fetch $ FileText filePath
        pure $
          case Parser.parseText Parser.module_ text filePath of
            Right ((module_, header), errorsAndDefinitions) -> do
              let
                (errors, definitions) =
                  partitionEithers errorsAndDefinitions

                header' =
                  case module_ of
                    Builtin.Module ->
                      header

                    _ ->
                      header
                        { Module._imports =
                          Module.Import
                            { _span = Span.Absolute 0 0
                            , _module = Builtin.Module
                            , _alias = "Sixten.Builtin"
                            , _importedNames = Module.AllExposed
                            }
                          : Module._imports header
                        }
              ((module_, header', definitions), map (Error.Parse filePath) errors)

            Left err ->
              ((Name.Module $ fromString filePath, mempty, mempty), pure $ Error.Parse filePath err)

    ModuleHeader module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, header, _) <- fetch $ ParsedFile filePath
          errors <- fmap concat $ forM (Module._imports header) $ \import_ -> do
            maybeModuleFile <- fetch $ Query.ModuleFile $ Mapped.Query $ Module._module import_
            pure [Error.ImportNotFound module_ import_ | isNothing maybeModuleFile]
          pure (header, errors)

    ImportedNames module_ subQuery ->
      noError $ Mapped.rule (ImportedNames module_) subQuery $ do
        header <- fetch $ ModuleHeader module_
        scopes <- forM (Module._imports header) $ \import_ -> do
          importedHeader <- fetch $ ModuleHeader $ Module._module import_
          ((_, publicScope, _), _) <- fetch $ Scopes $ Module._module import_
          pure $
            Resolution.importedNames import_ $
            Resolution.exposedNames (Module._exposedNames importedHeader) publicScope

        pure $ foldl' (HashMap.unionWith (<>)) mempty scopes

    NameAliases module_ ->
      noError $ do
        importedNames <- fetch $ ImportedNames module_ Mapped.Map
        ((localScope, _, _), _) <- fetch $ Scopes module_
        pure $ Scope.aliases $ HashMap.unionWith (<>) localScope importedNames

    ParsedDefinition module_ subQuery ->
      noError $ Mapped.rule (ParsedDefinition module_) subQuery $ do
        maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, _, defs) <- fetch $ ParsedFile filePath
          pure $ HashMap.fromList
            [ ((Presyntax.key def, name), def)
            | (_, (name, def)) <- defs
            ]

    ModulePositionMap module_ ->
      noError $ do
        spans <- fetch $ ModuleSpanMap module_
        pure $ (\(Span.Absolute start _) -> start) <$> spans

    ModuleSpanMap module_ ->
      noError $ do
        maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          text <- fetch $ FileText filePath
          (_, _, defs) <- fetch $ ParsedFile filePath
          let
            go = \case
              [] ->
                []

              [(loc, (name, def))] ->
                [((Presyntax.key def, name), Span.Absolute loc $ Position.Absolute $ Text.lengthWord16 text)]

              (loc1, (name, def)):defs'@((loc2, _):_) ->
                ((Presyntax.key def, name), Span.Absolute loc1 loc2) : go defs'

          pure $ HashMap.fromList $ go defs

    Scopes module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, _, defs) <- fetch $ ParsedFile filePath
          pure $ Resolution.moduleScopes module_ $ snd <$> defs

    ResolvedName (Scope.KeyedName key (Name.Qualified module_ keyName)) prename ->
      noError $ do
        (_, scopes) <- fetch $ Scopes module_
        importedScopeEntry <- fetchImportedName module_ prename
        pure $
          case HashMap.lookup (keyName, key) scopes of
            Nothing ->
              importedScopeEntry

            Just (scope, _) ->
              importedScopeEntry <> HashMap.lookup prename scope

    IsDefinitionVisible (Scope.KeyedName key (Name.Qualified keyModule keyName)) qualifiedName@(Name.Qualified nameModule _)
      | keyModule == nameModule ->
        noError $ do
          (_, scopes) <- fetch $ Scopes keyModule
          let
            (_, visibility) =
              HashMap.lookupDefault mempty (keyName, key) scopes

          pure $
            HashMap.lookup qualifiedName visibility == Just Scope.Definition

      | otherwise ->
        noError $ do
          ((_, _, finalVisibility), _) <- fetch $ Scopes nameModule
          pure $
            HashMap.lookup qualifiedName finalVisibility == Just Scope.Definition

    ElaboratingDefinition keyedName@(Scope.KeyedName key qualifiedName@(Name.Qualified module_ name)) ->
      nonInput $ do
        mdef <- fetch $ ParsedDefinition module_ $ Mapped.Query (key, name)
        case mdef of
          Nothing ->
            pure (Nothing, mempty)

          Just def -> do
            mtype <-
              case key of
                Scope.Type ->
                  pure $ Just Builtin.type_

                Scope.Definition -> do
                  mtype <- fetch $ ParsedDefinition module_ $ Mapped.Query (Scope.Type, name)
                  forM mtype $ \_ -> do
                    fetch $ ElaboratedType qualifiedName

            case mtype of
              Nothing ->
                runElaborator keyedName $ Elaboration.inferTopLevelDefinition keyedName def

              Just type_ ->
                runElaborator keyedName $ do
                  typeValue <- Evaluation.evaluate (Environment.empty keyedName) type_
                  ((def', metaVars), errs) <- Elaboration.checkTopLevelDefinition keyedName def typeValue
                  pure ((def', type_, metaVars), errs)

    ElaboratedType Builtin.TypeName ->
      nonInput $
        pure (Syntax.Global Builtin.TypeName, mempty)

    ElaboratedType qualifiedName ->
      nonInput $ do
        let
          typeKey =
            Scope.KeyedName Scope.Type qualifiedName
        mtypeDecl <- fetch $ ElaboratingDefinition typeKey
        case mtypeDecl of
          Nothing -> do
            mdef <- fetch $ ElaboratedDefinition qualifiedName
            case mdef of
              Nothing ->
                panic $ "ElaboratedType: No type or definition " <> show qualifiedName

              Just (_, type_) ->
                pure (type_, mempty)

          Just (typeDecl, type_, metaVars) -> do
            (maybeResult, errs) <- runElaborator typeKey $
              Elaboration.checkDefinitionMetaSolutions typeKey typeDecl type_ metaVars
            pure $
              case maybeResult of
                Nothing ->
                  ( Syntax.App
                    (Syntax.Global Builtin.fail)
                    Explicit
                    (Syntax.Global Builtin.TypeName)
                  , errs
                  )

                Just (Syntax.TypeDeclaration result, _) ->
                  (result, errs)

                Just _ ->
                  panic "ElaboratedType: Not a type declaration"

    ElaboratedDefinition qualifiedName ->
      nonInput $ do
        let
          defKey =
            Scope.KeyedName Scope.Definition qualifiedName
        maybeDef <- fetch $ ElaboratingDefinition defKey
        case maybeDef of
          Nothing ->
            pure (Nothing, mempty)

          Just (def, type_, metaVars) -> do
            runElaborator defKey $
              Elaboration.checkDefinitionMetaSolutions defKey def type_ metaVars

    ConstructorType (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        def <- fetch $ ElaboratedDefinition dataTypeName
        case def of
          Just (Syntax.DataDefinition tele, _) -> do
            let
              go :: Telescope Syntax.Type Syntax.ConstructorDefinitions v -> Telescope Syntax.Type Syntax.Type v
              go tele' =
                case tele' of
                  Telescope.Empty (Syntax.ConstructorDefinitions constrs) ->
                    Telescope.Empty $
                      HashMap.lookupDefault
                        (panic "ConstructorType: no such constructor")
                        constr
                        constrs

                  Telescope.Extend paramName paramType plicity tele'' ->
                    Telescope.Extend paramName paramType (implicitise plicity) $ go tele''

            pure $ go tele

          _ ->
            panic "ConstructorType: none-datatype"

    KeyedNameSpan (Scope.KeyedName key (Name.Qualified module_ name@(Name textName))) ->
      noError $ do
        positions <- fetch $ ModulePositionMap module_
        maybeFilePath <- fetch $ Query.ModuleFile $ Mapped.Query module_
        pure $ case maybeFilePath of
          Nothing ->
            ( "<no file>"
            , Span.Absolute 0 0
            )

          Just filePath ->
            ( filePath
            , case HashMap.lookup (key, name) positions of
              Nothing ->
                Span.Absolute 0 0

              Just position ->
                Span.Absolute
                  position
                  (position + Position.Absolute (Text.lengthWord16 textName))
            )

    Occurrences scopeKey@(Scope.KeyedName key name) ->
      nonInput $
      fmap (first fold) $
      runElaborator scopeKey $ do
        intervals <- Occurrences.run $
          Occurrences.definitionOccurrences
            (Environment.empty scopeKey)
            key
            name
        pure (intervals, mempty)

  where
    input :: Functor m => m a -> m ((a, TaskKind), [Error])
    input = fmap ((, mempty) . (, Input))

    noError :: Functor m => m a -> m ((a, TaskKind), [Error])
    noError = fmap ((, mempty) . (, NonInput))

    nonInput :: Functor m => m (a, [Error]) -> m ((a, TaskKind), [Error])
    nonInput = fmap (first (, NonInput))

    runElaborator
      :: Scope.KeyedName
      -> M (a, [Error])
      -> Task Query (Maybe a, [Error])
    runElaborator key m = do
      eitherResult <- runM m
      pure $
        case eitherResult of
          Left err ->
            ( Nothing
            , pure $
              Error.Elaboration key $
              Error.Spanned (Span.Relative 0 0) err
            )

          Right (result, errs) ->
            (Just result, errs)
