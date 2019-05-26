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
        pure $ HashMap.fromList $ Resolution.keyed <$> defs

    ParsedDefinition (Resolution.KeyedName (Name.Qualified module_ name) key) ->
      noError $ do
        defs <- fetch $ ParsedModuleMap module_
        pure $ HashMap.lookup (name, key) defs

    Scopes module_ -> do
      defs <- fetch $ ParsedModule module_
      pure $ Resolution.moduleScopes defs

    Visibility (Resolution.KeyedName (Name.Qualified module_ keyName) key) (Presyntax.Name name) ->
      noError $ do
        scopes <- fetch $ Scopes module_
        let
          scope = scopes HashMap.! (keyName, key)

        pure $ HashMap.lookup (Name name) scope

    -- TODO
    ResolvedName _ name
      | name == "Type" -> pure (Just Builtin.typeName, mempty)

    ResolvedName key@(Resolution.KeyedName (Name.Qualified module_ _) _) prename@(Presyntax.Name name) ->
      noError $ do
        visibility <- fetch $ Query.Visibility key prename
        case visibility of
          Nothing ->
            pure Nothing

          Just _ ->
            pure $ Just $ Name.Qualified module_ (Name name)

    ElaboratedType name
      | name == Builtin.typeName ->
        pure ((Syntax.Global Builtin.typeName, mempty), mempty)

      | otherwise -> do
        let
          key =
            Resolution.KeyedName name Resolution.TypeDeclaration
        mtype <- fetch $ ParsedDefinition key
        case mtype of
          Nothing -> do
            mdef <- fetch $ ElaboratedDefinition name
            case mdef of
              Nothing ->
                panic "ElaboratedType: No type or definition"

              Just (_, type_, metas) ->
                pure ((type_, metas), mempty)

          Just type_ -> do
            (maybeResult, errs) <- runM $
              Elaboration.checkTopLevel key type_ Builtin.type_
            case maybeResult of
              Nothing ->
                pure
                  ( ( Syntax.App
                      (Syntax.Global Builtin.fail)
                      (Syntax.Global Builtin.typeName)
                    , mempty
                    )
                  , errs
                  )

              Just result ->
                pure (result, errs) -- TODO metas

    ElaboratedDefinition name
      | name == Builtin.typeName ->
        pure (Nothing, mempty)
      | otherwise -> do
        let
          defKey =
            Resolution.KeyedName name Resolution.ConstantDefinition
        mdef <- fetch $ ParsedDefinition defKey
        case mdef of
          Nothing ->
            pure (Nothing, mempty)

          Just def -> do
            let
              typeKey =
                Resolution.KeyedName name Resolution.TypeDeclaration
            mtype <- fetch $ ParsedDefinition typeKey
            case mtype of
              Nothing ->
                runM $ Elaboration.inferTopLevel defKey def

              Just _ -> do
                (type_, typeMetas) <- fetch $ ElaboratedType name
                runM $ do
                  typeValue <- Evaluation.evaluate Domain.empty type_
                  (def', defMetas) <- Elaboration.checkTopLevel defKey def typeValue
                  pure (def', type_, defMetas <> typeMetas)

  where
    noError :: Functor m => m a -> m (a, [Error])
    noError = fmap (, mempty)
