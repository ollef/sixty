{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language TupleSections #-}
module Rules where

import Protolude hiding (force)

import qualified Data.HashMap.Lazy as HashMap
import Rock
import qualified Text.Parsix as Parsix

import qualified Builtin
import qualified Context
import qualified Elaboration
import Error (Error)
import qualified Error
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

    ParsedDefinition module_ key ->
      noError $ do
        defs <- fetch $ ParsedModuleMap module_
        pure $ HashMap.lookup key defs

    Scopes module_ -> do
      defs <- fetch $ ParsedModule module_
      pure $ Resolution.moduleScopes defs

    Visibility module_ key (Presyntax.Name name) ->
      noError $ do
        scopes <- fetch $ Scopes module_
        let
          scope = scopes HashMap.! key

        pure $ HashMap.lookup (Name name) scope

    -- TODO
    ResolvedName _ _ name
      | name == "Type" -> pure (Just Builtin.typeName, mempty)

    ResolvedName module_ key prename@(Presyntax.Name name) ->
      noError $ do
        visibility <- fetch $ Query.Visibility module_ key prename
        case visibility of
          Nothing ->
            pure Nothing

          Just _ ->
            pure $ Just $ Name.Qualified module_ (Name name)

    ElaboratedType qualifiedName@(Name.Qualified module_ name)
      | qualifiedName == Builtin.typeName ->
        pure (Syntax.Global Builtin.typeName, mempty)

      | otherwise -> do
        mtype <- fetch $ ParsedDefinition module_ $ Resolution.TypeDeclaration name
        case mtype of
          Nothing -> do
            mdef <- fetch $ ElaboratedDefinition qualifiedName
            case mdef of
              Nothing ->
                panic "ElaboratedType: No type or definition"

              Just (_, type_) ->
                pure (type_, mempty)

          Just type_ -> do
            (maybeResult, errs) <-
              runM $ do
                context <- Context.empty module_ $ Resolution.TypeDeclaration name
                Elaboration.check context type_ Builtin.type_
            case maybeResult of
              Nothing ->
                pure
                  ( Syntax.App
                    (Syntax.Global Builtin.fail)
                    (Syntax.Global Builtin.typeName)
                  , errs
                  )

              Just result ->
                pure (result, errs)

    ElaboratedDefinition qualifiedName@(Name.Qualified module_ name)
      | qualifiedName == Builtin.typeName ->
        pure (Nothing, mempty)
      | otherwise -> do
        mdef <- fetch $ ParsedDefinition module_ $ Resolution.ConstantDefinition name
        case mdef of
          Nothing ->
            pure (Nothing, mempty)

          Just def -> do
            mtype <- fetch $ ParsedDefinition module_ $ Resolution.TypeDeclaration name
            case mtype of
              Nothing ->
                fmap (first join) $ runM $ do
                  context <- Context.empty module_ $ Resolution.ConstantDefinition name
                  Elaboration.Inferred def' typeValue <- Elaboration.infer context def
                  typeValue' <- force typeValue
                  type_ <- Elaboration.readback context typeValue'
                  pure $ Just (def', type_)

              Just _ -> do
                type_ <- fetch $ ElaboratedType qualifiedName
                fmap (first join) $ runM $ do
                  context <- Context.empty module_ $ Resolution.ConstantDefinition name
                  typeValue <- Elaboration.evaluate context type_
                  def' <- Elaboration.check context def typeValue
                  pure $ Just (def', type_)

  where
    noError :: Functor m => m a -> m (a, [Error])
    noError = fmap (, mempty)
