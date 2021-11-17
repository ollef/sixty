{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Rules where

import qualified AssemblyToLLVM
import qualified Builtin
import qualified ClosureConversion
import qualified ClosureConverted.Context
import qualified ClosureConverted.Representation
import qualified ClosureConverted.Syntax
import qualified ClosureConverted.TypeOf as ClosureConverted
import qualified ClosureConvertedToAssembly
import Control.Exception.Lifted
import Core.Binding (Binding)
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.OrderedHashSet as OrderedHashSet
import qualified Data.Text as Text
import qualified Data.Text.Unsafe as Text
import qualified Elaboration
import qualified Environment
import Error (Error)
import qualified Error
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified LambdaLifting
import qualified Lexer
import qualified Module
import Monad
import qualified Name
import qualified Occurrences
import qualified Parser
import qualified Paths_sixty as Paths
import Plicity
import qualified Position
import Protolude hiding (force, moduleName, try, (<.>))
import Query
import qualified Query.Mapped as Mapped
import qualified Resolution
import Rock
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import System.FilePath
import Telescope (Telescope)
import qualified Telescope

rules :: [FilePath] -> HashSet FilePath -> (FilePath -> IO Text) -> GenRules (Writer [Error] (Writer TaskKind Query)) Query
rules sourceDirectories files readFile_ (Writer (Writer query)) =
  case query of
    SourceDirectories ->
      input $
        pure $
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
        let candidates =
              [ candidate
              | sourceDirectory <- sourceDirectories_
              , let candidate =
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
            filePath1 : filePath2 : _ ->
              ( Just filePath1
              , [Error.MultipleFilesWithModuleName moduleName filePath1 filePath2]
              )
    ParsedFile filePath ->
      nonInput $ do
        text <- fetch $ FileText filePath
        fileModuleName <- moduleNameFromFilePath
        case Parser.parseTokens Parser.module_ $ Lexer.lexText text of
          Right ((maybeModuleName, header), errorsAndDefinitions) -> do
            let (parseErrors, definitions) =
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
                          } :
                        Module._imports header
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
                    ]
                      ++ errors
                  )
          Left err ->
            pure ((fileModuleName, mempty, mempty), pure $ Error.Parse filePath err)
      where
        moduleNameFromFilePath :: Task Query Name.Module
        moduleNameFromFilePath = do
          sourceDirectories_ <- fetch SourceDirectories
          let candidates =
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
                firstCandidate : _ ->
                  firstCandidate
    ModuleDefinitions module_ ->
      noError $ do
        maybeFile <- fetch $ ModuleFile module_
        fmap (OrderedHashSet.fromList . fold) $
          forM maybeFile $ \file -> do
            (_, _, defs) <- fetch $ ParsedFile file
            pure $ fst . snd <$> defs
    ModuleHeader module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $
          forM maybeFilePath $ \filePath -> do
            (_, header, _) <- fetch $ ParsedFile filePath
            errors <- fmap concat $
              forM (Module._imports header) $ \import_ -> do
                maybeModuleFile <- fetch $ Query.ModuleFile $ Module._module import_
                pure [Error.ImportNotFound module_ import_ | isNothing maybeModuleFile]
            pure (header, errors)
    ImportedNames module_ subQuery ->
      noError $
        Mapped.rule (ImportedNames module_) subQuery $ do
          header <- fetch $ ModuleHeader module_
          scopes <- forM (Module._imports header) $ \import_ -> do
            importedHeader <- fetch $ ModuleHeader $ Module._module import_
            (_, publicScope) <- fetch $ ModuleScope $ Module._module import_
            pure $
              Resolution.importedNames import_ $
                Resolution.exposedNames (Module._exposedNames importedHeader) publicScope

          pure $ foldl' (HashMap.unionWith (<>)) mempty scopes
    NameAliases module_ ->
      noError $ do
        importedNames <- fetch $ ImportedNames module_ Mapped.Map
        (localScope, _) <- fetch $ ModuleScope module_
        pure $ Scope.aliases $ HashMap.unionWith (<>) localScope importedNames
    ParsedDefinition module_ subQuery ->
      noError $
        Mapped.rule (ParsedDefinition module_) subQuery $ do
          maybeFilePath <- fetch $ Query.ModuleFile module_
          fmap fold $
            forM maybeFilePath $ \filePath -> do
              (_, _, defs) <- fetch $ ParsedFile filePath
              pure $
                HashMap.fromListWith
                  (\_new old -> old)
                  [ ((Surface.entityKind def, name), def)
                  | (_, (name, def)) <- defs
                  ]
    ModulePositionMap module_ ->
      noError $ do
        spans <- fetch $ ModuleSpanMap module_
        pure $ (\(Span.Absolute start _) -> start) <$> spans
    ModuleSpanMap module_ ->
      noError $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $
          forM maybeFilePath $ \filePath -> do
            text <- fetch $ FileText filePath
            (_, _, defs) <- fetch $ ParsedFile filePath
            let go = \case
                  [] ->
                    []
                  [(loc, (name, def))] ->
                    [((Surface.entityKind def, name), Span.Absolute loc $ Position.Absolute $ Text.lengthWord16 text)]
                  (loc1, (name, def)) : defs'@((loc2, _) : _) ->
                    ((Surface.entityKind def, name), Span.Absolute loc1 loc2) : go defs'

            pure $ HashMap.fromListWith (\_new old -> old) $ go defs
    ModuleScope module_ ->
      nonInput $ do
        maybeFilePath <- fetch $ Query.ModuleFile module_
        fmap fold $
          forM maybeFilePath $ \filePath -> do
            (_, _, defs) <- fetch $ ParsedFile filePath
            pure $ Resolution.moduleScopes module_ defs
    ResolvedName module_ surfaceName ->
      noError $ do
        (privateScope, _) <- fetch $ ModuleScope module_
        importedScopeEntry <- fetchImportedName module_ surfaceName
        pure $
          case HashMap.lookup surfaceName privateScope of
            Nothing ->
              importedScopeEntry
            Just localEntry ->
              importedScopeEntry <> Just localEntry
    ElaboratingDefinition entityKind qualifiedName@(Name.Qualified module_ name) ->
      nonInput $ do
        mdef <- fetch $ ParsedDefinition module_ $ Mapped.Query (entityKind, name)
        case mdef of
          Nothing ->
            pure (Nothing, mempty)
          Just def -> do
            mtype <-
              case entityKind of
                Scope.Type ->
                  pure $ Just Builtin.type_
                Scope.Definition -> do
                  mtype <- fetch $ ParsedDefinition module_ $ Mapped.Query (Scope.Type, name)
                  forM mtype $ \_ ->
                    fetch $ ElaboratedType qualifiedName

            runElaboratorWithDefault Nothing entityKind qualifiedName $
              case mtype of
                Nothing ->
                  first Just <$> Elaboration.inferTopLevelDefinition entityKind qualifiedName def
                Just type_ -> do
                  typeValue <- Evaluation.evaluate Environment.empty type_
                  ((def', metaVars), errs) <- Elaboration.checkTopLevelDefinition entityKind qualifiedName def typeValue
                  pure (Just (def', type_, metaVars), errs)
    ElaboratedType Builtin.TypeName ->
      nonInput $
        pure (Syntax.Global Builtin.TypeName, mempty)
    ElaboratedType qualifiedName ->
      nonInput $ do
        mtypeDecl <- fetch $ ElaboratingDefinition Scope.Type qualifiedName
        case mtypeDecl of
          Nothing -> do
            (_, type_) <- fetch $ ElaboratedDefinition qualifiedName
            pure
              ( type_
              , mempty
              )
          Just (typeDecl, type_, metaVars) -> do
            (typeDecl', errs) <-
              runElaboratorWithDefault (Syntax.TypeDeclaration $ Builtin.fail Builtin.type_, Builtin.fail Builtin.type_) Scope.Type qualifiedName $
                Elaboration.checkDefinitionMetaSolutions Scope.Type qualifiedName typeDecl type_ metaVars
            pure $
              case typeDecl' of
                (Syntax.TypeDeclaration result, _) ->
                  (result, errs)
                _ ->
                  panic "ElaboratedType: Not a type declaration"
    ElaboratedDefinition qualifiedName ->
      nonInput $ do
        maybeDef <- fetch $ ElaboratingDefinition Scope.Definition qualifiedName
        case maybeDef of
          Nothing -> do
            type_ <- fetch $ ElaboratedType qualifiedName
            pure ((Syntax.TypeDeclaration type_, Builtin.type_), mempty)
          Just (def, type_, metaVars) -> do
            let fail = (Syntax.TypeDeclaration $ Builtin.fail Builtin.type_, Builtin.fail Builtin.type_)
            runElaboratorWithDefault fail Scope.Definition qualifiedName $
              Elaboration.checkDefinitionMetaSolutions Scope.Definition qualifiedName def type_ metaVars
    ConstructorType (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        (def, _) <- fetch $ ElaboratedDefinition dataTypeName
        let fail =
              Builtin.fail $ Builtin.fail Builtin.type_

        case def of
          Syntax.DataDefinition _ tele -> do
            let go :: Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v -> Telescope Binding Syntax.Type Syntax.Type v
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
    DefinitionPosition entityKind (Name.Qualified module_ name) ->
      noError $ do
        positions <- fetch $ ModulePositionMap module_
        maybeFilePath <- fetch $ Query.ModuleFile module_
        pure
          ( fromMaybe "<no file>" maybeFilePath
          , HashMap.lookupDefault 0 (entityKind, name) positions
          )
    Occurrences entityKind name ->
      noError $
        runM $
          Occurrences.run $
            Occurrences.definitionOccurrences
              Environment.empty
              entityKind
              name
    LambdaLifted qualifiedName ->
      noError $ do
        (definition, _) <- fetch $ ElaboratedDefinition qualifiedName
        runM $ LambdaLifting.liftDefinition qualifiedName definition
    LambdaLiftedDefinition (Name.Lifted qualifiedName index) ->
      noError $ do
        (def, liftedDefs) <- fetch $ LambdaLifted qualifiedName
        pure $
          case index of
            0 -> def
            _ ->
              LambdaLifted.ConstantDefinition $
                IntMap.lookupDefault
                  (Telescope.Empty $ LambdaLifted.Global $ Name.Lifted Builtin.FailName 0)
                  index
                  liftedDefs
    LambdaLiftedModuleDefinitions module_ ->
      noError $ do
        names <- fetch $ ModuleDefinitions module_
        fmap (OrderedHashSet.fromList . concat) $
          forM (toList names) $ \name -> do
            let qualifiedName =
                  Name.Qualified module_ name
            (_, extras) <- fetch $ LambdaLifted qualifiedName
            pure $ Name.Lifted qualifiedName <$> 0 : IntMap.keys extras
    ClosureConverted name ->
      noError $ do
        definition <- fetch $ LambdaLiftedDefinition name
        ClosureConversion.convertDefinition definition
    ClosureConvertedType name ->
      noError $ do
        definition <- fetch $ ClosureConverted name
        runM $ ClosureConverted.typeOfDefinition ClosureConverted.Context.empty definition
    ClosureConvertedConstructorType (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        definition <- fetch $ ClosureConverted $ Name.Lifted dataTypeName 0
        case definition of
          ClosureConverted.Syntax.DataDefinition _ (ClosureConverted.Syntax.ConstructorDefinitions constrs) ->
            pure $
              Telescope.Empty $
                OrderedHashMap.lookupDefault
                  (panic "ClosureConvertedConstructorType: no such constructor")
                  constr
                  constrs
          ClosureConverted.Syntax.ParameterisedDataDefinition _ tele -> do
            let go ::
                  Telescope name ClosureConverted.Syntax.Type ClosureConverted.Syntax.ConstructorDefinitions v ->
                  Telescope name ClosureConverted.Syntax.Type ClosureConverted.Syntax.Type v
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
    ClosureConvertedSignature name ->
      noError $ do
        definition <- fetch $ ClosureConverted name
        runM $ ClosureConverted.Representation.signature definition
    ConstructorRepresentations dataTypeName ->
      noError $ ClosureConverted.Representation.constructorRepresentations dataTypeName
    ConstructorRepresentation (Name.QualifiedConstructor dataTypeName constr) ->
      noError $ do
        (boxity, maybeTags) <- fetch $ ConstructorRepresentations dataTypeName
        pure (boxity, (HashMap.! constr) <$> maybeTags)
    Assembly name ->
      noError $ do
        definition <- fetch $ ClosureConverted name
        runM $ ClosureConvertedToAssembly.generateDefinition name definition
    AssemblyModule module_ ->
      noError $ do
        names <- fetch $ LambdaLiftedModuleDefinitions module_
        assemblyDefinitions <- fmap concat $
          forM (toList names) $ \name -> do
            maybeAssembly <- fetch $ Assembly name
            pure $ toList $ (name,) <$> maybeAssembly
        moduleInitDefs <-
          runM $
            ClosureConvertedToAssembly.generateModuleInit module_ assemblyDefinitions
        pure $ moduleInitDefs <> assemblyDefinitions
    LLVMModule module_ ->
      noError $ do
        assemblyDefinitions <- fetch $ AssemblyModule module_
        pure $ AssemblyToLLVM.assembleModule module_ assemblyDefinitions
    LLVMModuleInitModule ->
      noError $ do
        inputFiles <- fetch Query.InputFiles
        moduleNames <- forM (toList inputFiles) $ \filePath -> do
          (moduleName, _, _) <- fetch $ Query.ParsedFile filePath
          pure moduleName

        assemblyDefinition <- runM $ ClosureConvertedToAssembly.generateModuleInits moduleNames

        pure $ AssemblyToLLVM.assembleModule "module_init" [(Name.Lifted "$module_init" 0, assemblyDefinition)]
  where
    input :: Functor m => m a -> m ((a, TaskKind), [Error])
    input = fmap ((,mempty) . (,Input))

    noError :: Functor m => m a -> m ((a, TaskKind), [Error])
    noError = fmap ((,mempty) . (,NonInput))

    nonInput :: Functor m => m (a, [Error]) -> m ((a, TaskKind), [Error])
    nonInput = fmap (first (,NonInput))

    runElaboratorWithDefault ::
      a ->
      Scope.EntityKind ->
      Name.Qualified ->
      M (a, [Error]) ->
      Task Query (a, [Error])
    runElaboratorWithDefault default_ entityKind defName m = do
      eitherResult <- try $ runM m
      pure $
        case eitherResult of
          Left err ->
            ( default_
            , pure $
                Error.Elaboration entityKind defName $
                  Error.Spanned (Span.Relative 0 0) err
            )
          Right (result, errs) ->
            (result, errs)
