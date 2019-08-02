{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List as List
import Data.String
import Data.Text.Unsafe as Text
import Rock

import qualified Builtin
import qualified Domain
import qualified Elaboration
import Error (Error)
import qualified Error
import qualified Evaluation
import qualified Module
import Monad
import Name (Name(Name))
import qualified Name
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

rules :: [FilePath] -> GenRules (Writer [Error] Query) Query
rules files (Writer query) =
  case query of
    InputFiles ->
      noError $ do
        builtinFile <- liftIO $ Paths.getDataFileName "builtin/Builtin.lx"
        pure $ builtinFile : files

    FileText filePath ->
      noError $ liftIO $ readFile filePath

    ModuleFile subQuery ->
      noError $ Mapped.rule ModuleFile subQuery $ do
        filePaths <- fetch InputFiles
        -- TODO check and remove duplicates
        moduleFiles <- forM filePaths $ \filePath -> do
          (module_, _, _) <- fetch $ ParsedFile filePath
          pure (module_, filePath)
        pure $ HashMap.fromList moduleFiles

    ParsedFile filePath -> do
      text <- fetch $ FileText filePath
      pure $
        case Parser.parseText Parser.module_ text filePath of
          Right ((module_, header), errorsAndDefinitions) -> do
            let
              (errors, definitions) =
                partitionEithers errorsAndDefinitions

              header'
                | module_ == Builtin.module_ =
                  header
                | otherwise =
                  header
                    { Module._imports =
                      Module.Import Builtin.module_ "Sixten.Builtin" Module.AllExposed
                      : Module._imports header
                    }
            ((module_, header', definitions), map (Error.Parse filePath) errors)

          Left err ->
            ((Name.Module $ fromString filePath, mempty, mempty), pure $ Error.Parse filePath err)
    ModuleHeader module_ ->
      noError $ do
        filePath <- fetchModuleFile module_
        (_, header, _) <- fetch $ ParsedFile filePath
        pure header

    ImportedNames module_ subQuery ->
      noError $ Mapped.rule (ImportedNames module_) subQuery $ do
        header <- fetch $ ModuleHeader module_
        scopes <- forM (Module._imports header) $ \import_ -> do
          importedHeader <- fetch $ ModuleHeader $ Module._module import_
          ((scope, _), _) <- fetch $ Scopes $ Module._module import_
          pure $
            Resolution.importedNames import_ $
            Resolution.exposedNames (Module._exposedNames importedHeader) scope

        pure $ foldl' (HashMap.unionWith (<>)) mempty scopes

    ParsedModuleMap module_ ->
      noError $ do
        filePath <- fetchModuleFile module_
        (_, _, defs) <- fetch $ ParsedFile filePath
        pure $ HashMap.fromList
          [ ((Presyntax.key def, name), def)
          | (_, (name, def)) <- defs
          ]

    ModulePositionMap module_ ->
      noError $ do
        filePath <- fetchModuleFile module_
        (_, _, defs) <- fetch $ ParsedFile filePath
        pure $
          HashMap.fromList
            [ ((Presyntax.key def, name), loc)
            | (loc, (name, def)) <- defs
            ]

    ParsedDefinition (Scope.KeyedName key (Name.Qualified module_ name)) ->
      noError $ do
        defs <- fetch $ ParsedModuleMap module_
        pure $ HashMap.lookup (key, name) defs

    Scopes module_ -> do
      filePath <- fetchModuleFile module_
      (_, _, defs) <- fetch $ ParsedFile filePath
      pure $ Resolution.moduleScopes module_ $ snd <$> defs

    ResolvedName (Scope.KeyedName key (Name.Qualified module_ keyName)) prename ->
      noError $ do
        (_, scopes) <- fetch $ Scopes module_
        importedScopeEntry <- fetchImportedName module_ prename
        let
          (scope, _) = scopes HashMap.! (keyName, key)

        pure $ importedScopeEntry <> HashMap.lookup prename scope

    Visibility (Scope.KeyedName key (Name.Qualified keyModule keyName)) qualifiedName@(Name.Qualified nameModule _)
      | keyModule == nameModule ->
        noError $ do
          (_, scopes) <- fetch $ Scopes keyModule
          let
            (_, visibility) = scopes HashMap.! (keyName, key)

          pure $
            fromMaybe (panic "Fetching Visibility for name without visibility") $
            HashMap.lookup qualifiedName visibility

      | otherwise ->
        noError $ do
          ((_, finalVisibility), _) <- fetch $ Scopes nameModule
          pure $
            fromMaybe (panic "Fetching Visibility for name without visibility") $
            HashMap.lookup qualifiedName finalVisibility

    ElaboratedType name
      | name == Builtin.typeName ->
        pure (Syntax.Global Builtin.typeName, mempty)

      | otherwise -> do
        let
          key =
            Scope.KeyedName Scope.Type name
        mtype <- fetch $ ParsedDefinition key
        case mtype of
          Nothing -> do
            mdef <- fetch $ ElaboratedDefinition name
            case mdef of
              Nothing ->
                panic $ "ElaboratedType: No type or definition " <> show key

              Just (_, type_) ->
                pure (type_, mempty)

          Just def -> do
            (maybeResult, errs) <- runElaborator key $
              Elaboration.checkTopLevelDefinition key def Builtin.type_
            pure $
              case maybeResult of
                Nothing ->
                  ( Syntax.App
                    (Syntax.Global Builtin.fail)
                    Explicit
                    (Syntax.Global Builtin.typeName)
                  , errs
                  )

                Just (Syntax.TypeDeclaration result) ->
                  (result, errs)

                Just _ ->
                  panic "ElaboratedType: Not a type declaration"

    ElaboratedDefinition name -> do
      let
        defKey =
          Scope.KeyedName Scope.Definition name
      mdef <- fetch $ ParsedDefinition defKey
      case mdef of
        Nothing ->
          pure (Nothing, mempty)

        Just def -> do
          let
            typeKey =
              Scope.KeyedName Scope.Type name
          mtype <- fetch $ ParsedDefinition typeKey
          case mtype of
            Nothing ->
              runElaborator defKey $ Elaboration.inferTopLevelDefinition defKey def

            Just _ -> do
              type_ <- fetch $ ElaboratedType name
              runElaborator defKey $ do
                typeValue <- Evaluation.evaluate (Domain.empty defKey) type_
                (def', errs) <- Elaboration.checkTopLevelDefinition defKey def typeValue
                pure ((def', type_), errs)

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
                      fromMaybe (panic "ConstructorType: no such constructor") $
                        List.lookup constr constrs

                  Telescope.Extend paramName paramType plicity tele'' ->
                    Telescope.Extend paramName paramType (implicitise plicity) $ go tele''

            pure $ go tele

          _ ->
            panic "ConstructorType: none-datatype"

    ErrorSpan err ->
      noError $
        case err of
          Error.Parse filePath parseError ->
            pure
              ( filePath
              , Span.Absolute (Error.position parseError) (Error.position parseError)
              )

          Error.DuplicateName keyedName ->
            fetch $ KeyedNameSpan keyedName

          Error.Elaboration keyedName (Error.Spanned relativeSpan _) -> do
            (file, Span.Absolute absolutePosition _) <- fetch $ KeyedNameSpan keyedName
            pure (file, Span.absoluteFrom absolutePosition relativeSpan)

    KeyedNameSpan (Scope.KeyedName key (Name.Qualified module_ name@(Name textName))) ->
      noError $ do
        positions <- fetch $ ModulePositionMap module_
        filePath <- fetchModuleFile module_
        pure
          ( filePath
          , case HashMap.lookup (key, name) positions of
            Nothing ->
              Span.Absolute 0 0

            Just position ->
              Span.Absolute
                position
                (position + Position.Absolute (Text.lengthWord16 textName))
          )
  where
    noError :: Functor m => m a -> m (a, [Error])
    noError = fmap (, mempty)

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
