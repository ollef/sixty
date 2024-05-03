module Elaboration.ZonkPostponedChecks where

import qualified Core.Syntax as Syntax
import qualified Elaboration.Postponed as Postponed
import Protolude hiding (IntMap)
import Telescope (Telescope)
import qualified Telescope

zonkDefinition :: Postponed.Checks -> Syntax.Definition -> Syntax.Definition
zonkDefinition postponed def =
  case def of
    Syntax.TypeDeclaration type_ ->
      Syntax.TypeDeclaration $ zonkTerm postponed type_
    Syntax.ConstantDefinition term ->
      Syntax.ConstantDefinition $ zonkTerm postponed term
    Syntax.DataDefinition boxity tele ->
      Syntax.DataDefinition boxity $ zonkDataDefinition postponed tele

zonkDataDefinition
  :: Postponed.Checks
  -> Telescope binding Syntax.Type Syntax.ConstructorDefinitions v
  -> Telescope binding Syntax.Type Syntax.ConstructorDefinitions v
zonkDataDefinition postponed tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constructorDefinitions) ->
      Telescope.Empty $ Syntax.ConstructorDefinitions $ zonkTerm postponed <$> constructorDefinitions
    Telescope.Extend binding type_ plicity tele' ->
      Telescope.Extend binding (zonkTerm postponed type_) plicity (zonkDataDefinition postponed tele')

zonkTerm :: Postponed.Checks -> Syntax.Term v -> Syntax.Term v
zonkTerm postponed term =
  case term of
    Syntax.Var _ ->
      term
    Syntax.Global _ ->
      term
    Syntax.Con _ ->
      term
    Syntax.Lit _ ->
      term
    Syntax.Meta _ ->
      term
    Syntax.PostponedCheck index term' ->
      case Postponed.lookup index postponed of
        Postponed.Unchecked {} ->
          zonkTerm postponed term'
        Postponed.Checking ->
          zonkTerm postponed term'
        Postponed.Checked term'' ->
          zonkTerm postponed $ Syntax.coerce term''
    Syntax.Lets lets ->
      Syntax.Lets $ zonkLets postponed lets
    Syntax.Pi binding domain plicity targetScope ->
      Syntax.Pi binding (zonkTerm postponed domain) plicity (zonkTerm postponed targetScope)
    Syntax.Fun domain plicity target ->
      Syntax.Fun (zonkTerm postponed domain) plicity (zonkTerm postponed target)
    Syntax.Lam binding type_ plicity bodyScope ->
      Syntax.Lam binding (zonkTerm postponed type_) plicity (zonkTerm postponed bodyScope)
    Syntax.App fun plicity arg ->
      Syntax.App (zonkTerm postponed fun) plicity (zonkTerm postponed arg)
    Syntax.Case scrutinee type_ branches defaultBranch ->
      Syntax.Case
        (zonkTerm postponed scrutinee)
        (zonkTerm postponed type_)
        (zonkBranches postponed branches)
        (zonkTerm postponed <$> defaultBranch)
    Syntax.Spanned span term' ->
      Syntax.Spanned span $ zonkTerm postponed term'

zonkLets :: Postponed.Checks -> Syntax.Lets v -> Syntax.Lets v
zonkLets postponed lets =
  case lets of
    Syntax.LetType binding type_ lets' ->
      Syntax.LetType binding (zonkTerm postponed type_) (zonkLets postponed lets')
    Syntax.Let binding index term lets' ->
      Syntax.Let binding index (zonkTerm postponed term) (zonkLets postponed lets')
    Syntax.In term ->
      Syntax.In $ zonkTerm postponed term

zonkBranches :: Postponed.Checks -> Syntax.Branches v -> Syntax.Branches v
zonkBranches postponed branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      Syntax.ConstructorBranches constructorTypeName $ map (zonkTelescope postponed) <$> constructorBranches
    Syntax.LiteralBranches literalBranches ->
      Syntax.LiteralBranches $ map (zonkTerm postponed) <$> literalBranches

zonkTelescope
  :: Postponed.Checks
  -> Telescope bindings Syntax.Type Syntax.Term v
  -> Telescope bindings Syntax.Type Syntax.Term v
zonkTelescope postponed tele =
  case tele of
    Telescope.Empty branch ->
      Telescope.Empty $ zonkTerm postponed branch
    Telescope.Extend bindings type_ plicity tele' ->
      Telescope.Extend bindings (zonkTerm postponed type_) plicity (zonkTelescope postponed tele')
