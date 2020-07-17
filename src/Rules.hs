{-# language ApplicativeDo #-}
{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding ((<.>), force, moduleName, try)

import Control.Exception.Lifted
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text
import Rock
import System.FilePath

import qualified ApplicativeNormalisation
import Binding (Binding)
import qualified Builtin
import qualified ClosureConversion
import qualified ClosureConverted.Context
import qualified ClosureConverted.Syntax
import qualified ClosureConverted.TypeOf as ClosureConverted
import qualified Elaboration
import qualified Environment
import Error (Error)
import qualified Error
import qualified Evaluation
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified LambdaLifting
import qualified Lexer
import qualified Module
import Monad
import Name (Name)
import qualified Name
import qualified Occurrences
import qualified Parser
import qualified Paths_sixty as Paths
import Plicity
import qualified Position
import qualified Surface.Syntax as Surface
import Query
import qualified Query.Mapped as Mapped
import qualified Resolution
import qualified Scope
import qualified Span
import qualified Core.Syntax as Syntax
import Telescope (Telescope)
import qualified Telescope

rules :: [FilePath] -> HashSet FilePath -> (FilePath -> IO Text) -> GenRules (Writer [Error] (Writer TaskKind Query)) Query
rules sourceDirectories files readFile_ (Writer (Writer query)) =
  case query of
    SourceDirectories ->
      input $ pure $
        case (sourceDirectories, HashSet.toList files) of
          -- A little hack to allow opening single source files without a project file
          ([], [file]) ->
            [takeDirectory file]

          _ ->
            sourceDirectories

    InputFiles ->
      input $ do
        builtinFile <- liftIO $ Paths.getDataFileName "builtin/Builtin.vix"
        pure $ HashSet.insert builtinFile files

    FileText filePath ->
      input $ liftIO $ readFile_ filePath

    ModuleFile Builtin.Module ->
      noError $
        Just <$> liftIO (Paths.getDataFileName "builtin/Builtin.vix")

    ModuleFile moduleName@(Name.Module moduleNameText) ->
      nonInput $ do
        files_ <- fetch InputFiles
        sourceDirectories_ <- fetch SourceDirectories
        let
          candidates =
            [ candidate
            | sourceDirectory <- sourceDirectories_
            , let
              candidate =
                sourceDirectory </> joinPath (map toS $ Text.splitOn "." moduleNameText) <.> "vix"
            , candidate `HashSet.member` files_
            ]

        pure $
          case candidates of
            [] ->
              (Nothing, mempty)

            [filePath] ->
              ( Just filePath
              , mempty
              )

            filePath1:filePath2:_ ->
              ( Just filePath1
              , [Error.MultipleFilesWithModuleName moduleName filePath1 filePath2]
              )

    ParsedFile filePath ->
      nonInput $ do
        text <- fetch $ FileText filePath
        fileModuleName <- moduleNameFromFilePath
        case Parser.parseTokens Parser.module_ $ Lexer.lexText text of
          Right ((maybeModuleName, header), errorsAndDefinitions) -> do
            let
              (parseErrors, definitions) =
                partitionEithers errorsAndDefinitions

              errors = Error.Parse filePath <$> parseErrors

              headerImportingBuiltins =
                header
                  { Module._imports =
                    Module.Import
                      { _span = Span.Absolute 0 0
                      , _module = Builtin.Module
                      , _alias = (Span.Absolute 0 0, "Sixten.Builtin")
                      , _importedNames = Module.AllExposed
                      }
                    : Module._imports header
                  }

            pure $
              case maybeModuleName of
                Nothing ->
                  ((fileModuleName, headerImportingBuiltins, definitions), errors)

                Just (_, Builtin.Module) ->
                  ((Builtin.Module, header, definitions), errors)

                Just (span, moduleName) ->
                  ( (moduleName, headerImportingBuiltins, definitions)
                  , [ Error.ModuleFileNameMismatch fileModuleName moduleName span filePath
                    | fileModuleName /= moduleName
                    ] ++
                    errors
                  )

          Left err ->
            pure ((fileModuleName, mempty, mempty), pure $ Error.Parse filePath err)
      where
        moduleNameFromFilePath :: Task Query Name.Module
        moduleNameFromFilePath = do
          sourceDirectories_ <- fetch SourceDirectories
          let
            candidates =
              [ toS $
                map (\c -> if isPathSeparator c then '.' else c) $
                dropWhile isPathSeparator $
                drop (length sourceDirectory) $
                dropExtension filePath
              | sourceDirectory <- sourceDirectories_
              , sourceDirectory `isPrefixOf` filePath
              ]

          pure $
            Name.Module $
            case candidates of
              [] ->
                toS filePath

              firstCandidate:_ ->
                firstCandidate

    ModuleHeader module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, header, _) <- fetch $ ParsedFile filePath
          errors <- fmap concat $ forM (Module._imports header) $ \import_ -> do
            maybeModuleFile <- fetch $ Query.ModuleFile $ Module._module import_
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
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, _, defs) <- fetch $ ParsedFile filePath
          pure $ HashMap.fromListWith (\_new old -> old)
            [ ((Surface.key def, name), def)
            | (_, (name, def)) <- defs
            ]

    ModulePositionMap module_ ->
      noError $ do
        spans <- fetch $ ModuleSpanMap module_
        pure $ (\(Span.Absolute start _) -> start) <$> spans

    ModuleSpanMap module_ ->
      noError $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          text <- fetch $ FileText filePath
          (_, _, defs) <- fetch $ ParsedFile filePath
          let
            go = \case
              [] ->
                []

              [(loc, (name, def))] ->
                [((Surface.key def, name), Span.Absolute loc $ Position.Absolute $ Text.lengthWord16 text)]

              (loc1, (name, def)):defs'@((loc2, _):_) ->
                ((Surface.key def, name), Span.Absolute loc1 loc2) : go defs'

          pure $ HashMap.fromListWith (\_new old -> old) $ go defs

    Scopes module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $ forM maybeFilePath $ \filePath -> do
          (_, _, defs) <- fetch $ ParsedFile filePath
          pure $ Resolution.moduleScopes module_ defs

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
                  forM mtype $ \_ ->
                    fetch $ ElaboratedType qualifiedName

            runElaborator keyedName $
              case mtype of
                Nothing ->
                  Elaboration.inferTopLevelDefinition keyedName def

                Just type_ -> do
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
            pure
              ( case mdef of
                Nothing ->
                  Syntax.App
                    (Syntax.Global Builtin.fail)
                    Explicit
                    (Syntax.Global Builtin.TypeName)

                Just (_, type_) ->
                  type_
              , mempty
              )

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

          Just (def, type_, metaVars) ->
            runElaborator defKey $
              Elaboration.checkDefinitionMetaSolutions defKey def type_ metaVars

    ConstructorType (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        def <- fetch $ ElaboratedDefinition dataTypeName
        let
          fail =
            Syntax.App (Syntax.Global Builtin.fail) Explicit $ Syntax.App (Syntax.Global Builtin.fail) Explicit (Syntax.Global Builtin.TypeName)

        case def of
          Just (Syntax.DataDefinition _ tele, _) -> do
            let
              go :: Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v -> Telescope Binding Syntax.Type Syntax.Type v
              go tele' =
                case tele' of
                  Telescope.Empty (Syntax.ConstructorDefinitions constrs) ->
                    Telescope.Empty $
                      OrderedHashMap.lookupDefault
                        fail
                        constr
                        constrs

                  Telescope.Extend paramName paramType plicity tele'' ->
                    Telescope.Extend paramName paramType (implicitise plicity) $ go tele''

            pure $ go tele

          _ ->
            pure $ Telescope.Empty fail

    KeyedNamePosition (Scope.KeyedName key (Name.Qualified module_ name)) ->
      noError $ do
        positions <- fetch $ ModulePositionMap module_
        maybeFilePath <- fetch $ Query.ModuleFile module_
        pure
          ( fromMaybe "<no file>" maybeFilePath
          , HashMap.lookupDefault 0 (key, name) positions
          )

    Occurrences scopeKey@(Scope.KeyedName key name) ->
      noError $ runM $ Occurrences.run $
        Occurrences.definitionOccurrences
          (Environment.empty scopeKey)
          key
          name

    LambdaLifted qualifiedName ->
      noError $ do
        maybeDef <- fetch $ ElaboratedDefinition qualifiedName
        case maybeDef of
          Nothing -> do
            type_ <- fetch $ ElaboratedType qualifiedName
            runM $
              LambdaLifting.liftDefinition qualifiedName (Syntax.TypeDeclaration type_)

          Just (def, _) ->
            runM $
              LambdaLifting.liftDefinition qualifiedName def

    LambdaLiftedDefinition (Name.Lifted qualifiedName index) ->
      noError $ do
        (def, liftedDefs) <- fetch $ LambdaLifted qualifiedName
        pure $
          case index of
            0 ->
              pure def

            _ ->
              LambdaLifted.ConstantDefinition <$>
                IntMap.lookup index liftedDefs

    ClosureConverted name ->
      noError $ do
        maybeDef <- fetch $ LambdaLiftedDefinition name
        mapM ClosureConversion.convertDefinition maybeDef

    ClosureConvertedType name@(Name.Lifted qualifiedName _) ->
      noError $ do
        maybeDef <- fetch $ ClosureConverted name
        case maybeDef of
          Nothing ->
            panic "ClosureConvertedType: no type"

          Just def ->
            runM $
              ClosureConverted.typeOfDefinition (ClosureConverted.Context.empty $ Scope.KeyedName Scope.Definition qualifiedName) def

    ClosureConvertedConstructorType (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        def <- fetch $ ClosureConverted $ Name.Lifted dataTypeName 0
        case def of
          Just (ClosureConverted.Syntax.DataDefinition (ClosureConverted.Syntax.ConstructorDefinitions constrs)) ->
            pure $
              Telescope.Empty $
              OrderedHashMap.lookupDefault
                (panic "ClosureConvertedConstructorType: no such constructor")
                constr
                constrs

          Just (ClosureConverted.Syntax.ParameterisedDataDefinition tele) -> do
            let
              go
                :: Telescope Name ClosureConverted.Syntax.Type ClosureConverted.Syntax.ConstructorDefinitions v
                -> Telescope Name ClosureConverted.Syntax.Type ClosureConverted.Syntax.Type v
              go tele' =
                case tele' of
                  Telescope.Empty (ClosureConverted.Syntax.ConstructorDefinitions constrs) ->
                    Telescope.Empty $
                      OrderedHashMap.lookupDefault
                        (panic "ClosureConvertedConstructorType: no such constructor")
                        constr
                        constrs

                  Telescope.Extend paramName paramType plicity tele'' ->
                    Telescope.Extend paramName paramType (implicitise plicity) $ go tele''

            pure $ go tele

          _ ->
            panic "ClosureConvertedConstructorType: none-datatype"

    Applicative name@(Name.Lifted qualifiedName _) ->
      noError $ do
        maybeDef <- fetch $ ClosureConverted name
        runM $ forM maybeDef $
          ApplicativeNormalisation.normaliseDefinition (Scope.KeyedName Scope.Definition qualifiedName)

    ConstructorTag (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        def <- fetch $ ElaboratedDefinition dataTypeName
        case def of
          Just (Syntax.DataDefinition _ tele, _) -> do
            let
              go :: Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v -> Maybe Int
              go tele' =
                case tele' of
                  Telescope.Empty (Syntax.ConstructorDefinitions constrs)
                    | OrderedHashMap.size constrs <= 1 ->
                      Nothing

                    | otherwise ->
                      List.elemIndex constr $ OrderedHashMap.keys constrs

                  Telescope.Extend _ _ _ tele'' ->
                    go tele''

            pure $ go tele

          _ ->
            pure Nothing

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
      eitherResult <- try $ runM m
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
