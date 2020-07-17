module Zonking where

import Protolude

import Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Environment
import qualified Evaluation
import qualified Meta
import Monad
import qualified Readback
import qualified Core.Syntax as Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

zonkTerm
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Void)))
  -> Syntax.Term v
  -> M (Syntax.Term v)
zonkTerm env metas term = do
  eitherValueOrTerm <- zonk env metas term
  case eitherValueOrTerm of
    Left value -> do
      term' <- Readback.readback env value
      zonkTerm env metas term'

    Right term' ->
      pure term'

zonkValue
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Void)))
  -> Syntax.Term v
  -> M Domain.Value
zonkValue env metas term = do
  eitherValueOrTerm <- zonk env metas term
  case eitherValueOrTerm of
    Left value ->
      pure value

    Right term' ->
      Evaluation.evaluate env term'

zonk
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Void)))
  -> Syntax.Term v
  -> M (Either Domain.Value (Syntax.Term v))
zonk env metas term =
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
          value <- Evaluation.evaluate (Environment.emptyFrom env) term'
          pure $ Left value

    Syntax.Let binding term' type_ scope -> do
      (env', _) <- Environment.extend env
      result <- Syntax.Let binding <$>
        zonkTerm env metas term' <*>
        zonkTerm env metas type_ <*>
        zonkTerm env' metas scope
      pure $ Right result

    Syntax.Pi binding domain plicity targetScope -> do
      (env', _) <- Environment.extend env
      result <- Syntax.Pi binding <$>
        zonkTerm env metas domain <*>
        pure plicity <*>
        zonkTerm env' metas targetScope
      pure $ Right result

    Syntax.Fun domain plicity target -> do
      result <- Syntax.Fun <$>
        zonkTerm env metas domain <*>
        pure plicity <*>
        zonkTerm env metas target
      pure $ Right result

    Syntax.Lam binding type_ plicity bodyScope -> do
      (env', _) <- Environment.extend env
      result <- Syntax.Lam binding <$>
        zonkTerm env metas type_ <*>
        pure plicity <*>
        zonkTerm env' metas bodyScope
      pure $ Right result

    Syntax.App fun plicity arg -> do
      funResult <- zonk env metas fun
      case funResult of
        Left funValue -> do
          argValue <- zonkValue env metas arg
          value <- Evaluation.apply funValue plicity argValue
          pure $ Left value

        Right fun' -> do
          result <- Syntax.App fun' plicity <$> zonkTerm env metas arg
          pure $ Right result

    Syntax.Case scrutinee branches defaultBranch -> do
      result <- Syntax.Case <$>
        zonkTerm env metas scrutinee <*>
        zonkBranches env metas branches <*>
        forM defaultBranch (zonkTerm env metas)
      pure $ Right result

    Syntax.Spanned span term' -> do
      result <- zonk env metas term'
      pure $ Syntax.Spanned span <$> result

zonkBranches
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Void)))
  -> Syntax.Branches v
  -> M (Syntax.Branches v)
zonkBranches env metas branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      Syntax.ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (mapM $ zonkTelescope env metas) constructorBranches

    Syntax.LiteralBranches literalBranches ->
      Syntax.LiteralBranches <$> OrderedHashMap.mapMUnordered (mapM $ zonkTerm env metas) literalBranches

zonkTelescope
  :: Domain.Environment v
  -> (Meta.Index -> M (Maybe (Syntax.Term Void)))
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M (Telescope Bindings Syntax.Type Syntax.Term v)
zonkTelescope env metas tele =
  case tele of
    Telescope.Empty branch ->
      Telescope.Empty <$> zonkTerm env metas branch

    Telescope.Extend bindings type_ plicity tele' -> do
      (env', _) <- Environment.extend env
      Telescope.Extend bindings <$>
        zonkTerm env metas type_ <*>
        pure plicity <*>
        zonkTelescope env' metas tele'
