{-# LANGUAGE RankNTypes #-}

module Core.Zonking where

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import qualified Index
import qualified Meta
import Monad
import qualified Postponement
import Protolude
import Telescope (Telescope)
import qualified Telescope

zonkDefinition
  :: Domain.Environment Index.Zero
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Definition
  -> M Syntax.Definition
zonkDefinition env metas postponed definition = case definition of
  Syntax.TypeDeclaration type_ ->
    Syntax.TypeDeclaration <$> zonkTerm env metas postponed type_
  Syntax.ConstantDefinition term ->
    Syntax.ConstantDefinition <$> zonkTerm env metas postponed term
  Syntax.DataDefinition boxity tele ->
    Syntax.DataDefinition boxity <$> zonkDataDefinition env metas postponed tele

zonkDataDefinition
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> M (Telescope Core.Binding.Binding Syntax.Type Syntax.ConstructorDefinitions v)
zonkDataDefinition env metas postponed tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constructorDefinitions) ->
      Telescope.Empty . Syntax.ConstructorDefinitions
        <$> OrderedHashMap.mapMUnordered (zonkTerm env metas postponed) constructorDefinitions
    Telescope.Extend bindings type_ plicity tele' -> do
      (env', _) <- Environment.extend env
      Telescope.Extend bindings
        <$> zonkTerm env metas postponed type_
        <*> pure plicity
        <*> zonkDataDefinition env' metas postponed tele'

zonkTerm
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Term v
  -> M (Syntax.Term v)
zonkTerm env metas postponed term = do
  eitherValueOrTerm <- zonk env metas postponed term
  case eitherValueOrTerm of
    Left value -> do
      term' <- Readback.readback env value
      zonkTerm env metas postponed term'
    Right term' ->
      pure term'

zonkValue
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Term v
  -> M Domain.Value
zonkValue env metas postponed term = do
  eitherValueOrTerm <- zonk env metas postponed term
  case eitherValueOrTerm of
    Left value ->
      pure value
    Right term' ->
      Evaluation.evaluate env term'

zonk
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Term v
  -> M (Either Domain.Value (Syntax.Term v))
zonk env metas postponed term =
  case term of
    Syntax.Var _ ->
      pure $ Right term
    Syntax.Global _ ->
      pure $ Right term
    Syntax.Con _ ->
      pure $ Right term
    Syntax.Lit _ ->
      pure $ Right term
    Syntax.Meta i -> do
      maybeTerm <- metas i
      case maybeTerm of
        Nothing ->
          pure $ Right term
        Just term' -> do
          value <- Evaluation.evaluate Environment.empty term'
          pure $ Left value
    Syntax.PostponedCheck index term' -> do
      maybeTerm <- postponed env index
      case maybeTerm of
        Nothing ->
          Right <$> zonkTerm env metas postponed term'
        Just term'' ->
          pure $ Right term''
    Syntax.Lets lets ->
      Right . Syntax.Lets <$> zonkLets env metas postponed lets
    Syntax.Pi binding domain plicity targetScope -> do
      (env', _) <- Environment.extend env
      result <-
        Syntax.Pi binding
          <$> zonkTerm env metas postponed domain
          <*> pure plicity
          <*> zonkTerm env' metas postponed targetScope
      pure $ Right result
    Syntax.Fun domain plicity target -> do
      result <-
        Syntax.Fun
          <$> zonkTerm env metas postponed domain
          <*> pure plicity
          <*> zonkTerm env metas postponed target
      pure $ Right result
    Syntax.Lam binding type_ plicity bodyScope -> do
      (env', _) <- Environment.extend env
      result <-
        Syntax.Lam binding
          <$> zonkTerm env metas postponed type_
          <*> pure plicity
          <*> zonkTerm env' metas postponed bodyScope
      pure $ Right result
    Syntax.App fun plicity arg -> do
      funResult <- zonk env metas postponed fun
      case funResult of
        Left funValue -> do
          argValue <- zonkValue env metas postponed arg
          value <- Evaluation.apply funValue plicity argValue
          pure $ Left value
        Right fun' -> do
          result <- Syntax.App fun' plicity <$> zonkTerm env metas postponed arg
          pure $ Right result
    Syntax.Case scrutinee type_ branches defaultBranch -> do
      result <-
        Syntax.Case
          <$> zonkTerm env metas postponed scrutinee
          <*> zonkTerm env metas postponed type_
          <*> zonkBranches env metas postponed branches
          <*> forM defaultBranch (zonkTerm env metas postponed)
      pure $ Right result
    Syntax.Spanned span term' -> do
      result <- zonk env metas postponed term'
      pure $ Syntax.Spanned span <$> result

zonkLets
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Lets v
  -> M (Syntax.Lets v)
zonkLets env metas postponed lets =
  case lets of
    Syntax.LetType binding type_ lets' -> do
      (env', _) <- Environment.extend env
      Syntax.LetType binding
        <$> zonkTerm env metas postponed type_
        <*> zonkLets env' metas postponed lets'
    Syntax.Let binding index term' lets' ->
      Syntax.Let binding index
        <$> zonkTerm env metas postponed term'
        <*> zonkLets env metas postponed lets'
    Syntax.In term ->
      Syntax.In <$> zonkTerm env metas postponed term

zonkBranches
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Syntax.Branches v
  -> M (Syntax.Branches v)
zonkBranches env metas postponed branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      Syntax.ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (mapM $ zonkTelescope env metas postponed) constructorBranches
    Syntax.LiteralBranches literalBranches ->
      Syntax.LiteralBranches <$> OrderedHashMap.mapMUnordered (mapM $ zonkTerm env metas postponed) literalBranches

zonkTelescope
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Index.Zero)))
  -> (forall v'. Domain.Environment v' -> Postponement.Index -> M (Maybe (Syntax.Term v')))
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M (Telescope Bindings Syntax.Type Syntax.Term v)
zonkTelescope env metas postponed tele =
  case tele of
    Telescope.Empty branch ->
      Telescope.Empty <$> zonkTerm env metas postponed branch
    Telescope.Extend bindings type_ plicity tele' -> do
      (env', _) <- Environment.extend env
      Telescope.Extend bindings
        <$> zonkTerm env metas postponed type_
        <*> pure plicity
        <*> zonkTelescope env' metas postponed tele'
