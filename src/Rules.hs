{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List as List
import Data.Text.Unsafe as Text
import Rock

import qualified Builtin
import qualified Domain
import qualified Elaboration
import Error (Error)
import qualified Error
import qualified Evaluation
import qualified Index
import Monad
import Name (Name(Name))
import qualified Name
import qualified Parser
import qualified Position
import Plicity
import qualified Presyntax
import Query
import qualified Resolution
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

rules :: GenRules (Writer [Error] Query) Query
rules (Writer query) =
  case query of
    FileText filePath ->
      noError $ liftIO $ readFile filePath

    ParsedModule module_ -> do
      let
        filePath =
          moduleFilePath module_

      text <- fetch $ FileText filePath
      pure $
        case Parser.parseText Parser.module_ text filePath of
          Right (_header, errorsAndDefinitions) -> do
            let
              (errors, definitions) =
                partitionEithers errorsAndDefinitions
            (definitions, map (Error.Parse filePath) errors)

          Left err ->
            (mempty, pure $ Error.Parse filePath err)

    ParsedModuleMap module_ ->
      noError $ do
        defs <- fetch $ ParsedModule module_
        pure $ HashMap.fromList
          [ ((Presyntax.key def, name), def)
          | (_, (name, def)) <- defs
          ]

    ModulePositionMap module_ ->
      noError $ do
        defs <- fetch $ ParsedModule module_
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
      defs <- fetch $ ParsedModule module_
      pure $ Resolution.moduleScopes module_ $ snd <$> defs

    -- TODO
    ResolvedName _ name
      | name == "Type" ->
        pure (Just $ Scope.Name Builtin.typeName, mempty)

    ResolvedName (Scope.KeyedName key (Name.Qualified module_ keyName)) prename ->
      noError $ do
        scopes <- fetch $ Scopes module_
        let
          (scope, _) = scopes HashMap.! (keyName, key)

        pure $ HashMap.lookup prename scope

    Visibility _ qualifiedName
      -- TODO
      | qualifiedName == Builtin.typeName ->
        pure (Scope.Type, mempty)

      | qualifiedName == Builtin.fail ->
        pure (Scope.Type, mempty)

    Visibility (Scope.KeyedName key (Name.Qualified module_ keyName)) qualifiedName ->
      noError $ do
        scopes <- fetch $ Scopes module_
        let
          (_, visibility) = scopes HashMap.! (keyName, key)

        pure $
          fromMaybe (panic "Fetching Visibility for name without visibility") $
          HashMap.lookup qualifiedName visibility

    ElaboratedType name
      -- TODO
      | name == Builtin.fail ->
        pure (Syntax.Pi "x" (Syntax.Global Builtin.typeName) Explicit $ Syntax.Var Index.Zero, mempty)

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
        pure
          ( moduleFilePath module_
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
