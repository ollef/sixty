{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import Rock
import qualified Text.Parsix as Parsix

import qualified Builtin
import qualified Domain
import qualified Elaboration
import Error (Error)
import qualified Error
import qualified Evaluation
import Monad
import Name (Name(Name))
import qualified Name
import qualified Parser
import qualified Presyntax
import Query
import qualified Resolution
import qualified Scope
import qualified Span
import qualified Syntax

rules :: GenRules (Writer [Error] Query) Query
rules (Writer query) =
  case query of
    ReadFile filePath ->
      noError $ liftIO $ readFile filePath

    ParsedModule (Name.Module module_) -> do
      let
        filePath =
          toS $ module_ <> ".lx"

      text <- fetch $ ReadFile filePath
      pure $ case Parser.parseText Parser.module_ text filePath of
        Parsix.Success definitions ->
          (definitions, mempty)

        Parsix.Failure err ->
          (mempty, pure $ Error.Parse err)

    ParsedModuleMap module_ ->
      noError $ do
        defs <- fetch $ ParsedModule module_
        pure $ HashMap.fromList $ Scope.keyed <$> defs

    ParsedDefinition (Scope.KeyedName key (Name.Qualified module_ name)) ->
      noError $ do
        defs <- fetch $ ParsedModuleMap module_
        pure $ HashMap.lookup (key, name) defs

    Scopes module_ -> do
      defs <- fetch $ ParsedModule module_
      pure $ Resolution.moduleScopes module_ defs

    Visibility (Scope.KeyedName key (Name.Qualified module_ keyName)) (Presyntax.Name name) ->
      noError $ do
        scopes <- fetch $ Scopes module_
        let
          scope = scopes HashMap.! (keyName, key)

        pure $ HashMap.lookup (Name name) scope

    -- TODO
    ResolvedName _ name
      | name == "Type" -> pure (Just Builtin.typeName, mempty)

    ResolvedName key@(Scope.KeyedName _ (Name.Qualified module_ _)) prename@(Presyntax.Name name) ->
      noError $ do
        visibility <- fetch $ Query.Visibility key prename
        case visibility of
          Nothing ->
            pure Nothing

          Just _ ->
            pure $ Just $ Name.Qualified module_ (Name name)

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
                panic "ElaboratedType: No type or definition"

              Just (_, type_) ->
                pure (type_, mempty)

          Just type_ -> do
            (maybeResult, errs) <- runElaborator key $
              Elaboration.checkTopLevel key type_ Builtin.type_
            pure $
              case maybeResult of
                Nothing ->
                  ( Syntax.App
                    (Syntax.Global Builtin.fail)
                    (Syntax.Global Builtin.typeName)
                  , errs
                  )

                Just result ->
                  (result, errs)

    ElaboratedDefinition name
      | name == Builtin.typeName ->
        pure (Nothing, mempty)
      | otherwise -> do
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
                runElaborator defKey $ Elaboration.inferTopLevel defKey def

              Just _ -> do
                type_ <- fetch $ ElaboratedType name
                runElaborator defKey $ do
                  typeValue <- Evaluation.evaluate Domain.empty type_
                  (def', errs) <- Elaboration.checkTopLevel defKey def typeValue
                  pure ((def', type_), errs)


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
