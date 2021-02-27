{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Elaboration.Meta where

import qualified Core.Syntax as Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Persist
import qualified Meta
import Orphans ()
import qualified Postponement
import Protolude hiding (IntMap, IntSet, State, state)
import qualified Span
import Telescope (Telescope)
import qualified Telescope

data Entry m
  = Unsolved (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | Solved (Syntax.Term Void) (Syntax.Type Void)
  | LazilySolved !(m (Syntax.Term Void)) (Syntax.Type Void)

entryType :: Entry m -> Syntax.Type Void
entryType entry =
  case entry of
    Unsolved _ type_ _ _ _ ->
      type_

    Solved _ _ type_ ->
      type_

    LazilySolved _ _ type_ ->
      type_

data State m = State
  { entries :: !(IntMap Meta.Index (Entry m))
  , nextIndex :: !Meta.Index
  }

empty :: State m
empty =
  State mempty $ Meta.Index 0

lookup :: Meta.Index -> State m -> Entry m
lookup index (State m _) =
  m IntMap.! index

insert :: Syntax.Term Void -> Int -> Span.Relative -> State m -> (State m, Meta.Index)
insert type_ arity span (State m index) =
  (State (IntMap.insert index (Unsolved type_ arity mempty span) m) (index + 1), index)

solve :: Meta.Index -> Syntax.Term Void -> State m -> (State m, (Int, IntSet Postponement.Index))
solve index term (State entries_ n) =
  (State entries' n, data_)
  where
    (data_, entries') =
      IntMap.alterF alter index entries_

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ Solved term type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

        Just LazilySolved {} ->
          panic "Solving an already solved meta variable"

lazilySolve :: Meta.Index -> m (Syntax.Term Void) -> State m -> (State m, (Int, IntSet Postponement.Index))
lazilySolve index mterm (State entries_ n) =
  (State entries' n, data_)
  where
    (data_, entries') =
      IntMap.alterF alter index entries_

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ LazilySolved mterm type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

        Just LazilySolved {} ->
          panic "Solving an already solved meta variable"

addPostponedIndex :: Meta.Index -> Postponement.Index -> State m -> State m
addPostponedIndex index postponementIndex (State m n) =
  State (IntMap.adjust adjust index m) n
  where
    adjust entry =
      case entry of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (IntSet.insert postponementIndex postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"

        LazilySolved {} ->
          panic "Adding postponement index to an already solved meta variable"

addPostponedIndices :: Meta.Index -> IntSet Postponement.Index -> State m -> State m
addPostponedIndices index postponementIndices (State m n) =
  State (IntMap.adjust adjust index m) n
  where
    adjust entry =
      case entry of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (postponementIndices <> postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"

        LazilySolved {} ->
          panic "Adding postponement index to an already solved meta variable"

-------------------------------------------------------------------------------
-- Eager entries

data EagerEntry
  = EagerUnsolved (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | EagerSolved (Syntax.Term Void) (Syntax.Type Void)
  deriving (Eq, Generic, Persist, Hashable)

data EagerState = EagerState
  { eagerEntries :: !(IntMap Meta.Index EagerEntry)
  , eagerNextIndex :: !Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

fromEagerState :: EagerState -> State m
fromEagerState (EagerState entries_ nextIndex_) =
  State (fromEagerEntry <$> entries_) nextIndex_

fromEagerEntry :: EagerEntry -> Entry m
fromEagerEntry entry =
  case entry of
    EagerUnsolved type_ arity postponements span ->
      Unsolved type_ arity postponements span

    EagerSolved term type_ ->
      Solved term type_

toEagerEntry :: Monad m => Entry m -> m EagerEntry
toEagerEntry entry =
  case entry of
    Unsolved type_ arity postponements span ->
      pure $ EagerUnsolved type_ arity postponements span

    Solved solution type_ ->
      pure $ EagerSolved solution type_

    LazilySolved msolution type_ -> do
      solution <- msolution
      pure $ EagerSolved solution type_

toEagerState :: Monad m => State m -> Syntax.Definition -> Maybe (Syntax.Type Void) -> m EagerState
toEagerState state definition maybeType = do
  entries_ <- go (definitionMetas definition <> foldMap termMetas maybeType) mempty
  pure EagerState
    { eagerEntries = entries_
    , eagerNextIndex = nextIndex state
    }
  where
    go todo done
      | IntMap.null todo' =
        pure done

      | otherwise = do
        newlyDone <-
          traverse
            (\case
              Unsolved type_ arity postponements span ->
                pure $ EagerUnsolved type_ arity postponements span

              Solved solution type_ ->
                pure $ EagerSolved solution type_

              LazilySolved msolution type_ -> do
                solution <- msolution
                pure $ EagerSolved solution type_
            )
            todo'

        let
          newTodo =
            foldMap
              (\case
                EagerUnsolved type_ _arity _postponements _span ->
                  termMetas type_

                EagerSolved solution _ ->
                  termMetas solution
              )
              newlyDone

        go newTodo (done <> newlyDone)
      where
        todo' =
          IntMap.difference (IntMap.fromSet (entries state IntMap.!) todo) done

definitionMetas :: Syntax.Definition -> IntSet Meta.Index
definitionMetas definition =
  case definition of
    Syntax.TypeDeclaration type_ ->
      termMetas type_

    Syntax.ConstantDefinition term ->
      termMetas term

    Syntax.DataDefinition _boxity tele ->
      dataDefinitionMetas tele

dataDefinitionMetas :: Telescope binding Syntax.Type Syntax.ConstructorDefinitions v -> IntSet Meta.Index
dataDefinitionMetas tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constructorDefinitions) ->
      foldMap termMetas constructorDefinitions

    Telescope.Extend _binding type_ _plixity tele' ->
      termMetas type_ <> dataDefinitionMetas tele'

termMetas :: Syntax.Term v -> IntSet Meta.Index
termMetas term =
  case term of
    Syntax.Var _ ->
      mempty

    Syntax.Global _ ->
      mempty

    Syntax.Con _ ->
      mempty

    Syntax.Lit _ ->
      mempty

    Syntax.Meta index ->
      IntSet.singleton index

    Syntax.PostponedCheck {} ->
      panic "Elaboration.Meta.termMetas: PostponedCheck"

    Syntax.Let _binding term' type_ body ->
      termMetas term' <> termMetas type_ <> termMetas body

    Syntax.Pi _binding domain _plicity target ->
      termMetas domain <> termMetas target

    Syntax.Fun domain _plicity target ->
      termMetas domain <> termMetas target

    Syntax.Lam _bindings type_ _plicity body ->
      termMetas type_ <> termMetas body

    Syntax.App function _plicity argument ->
      termMetas function <> termMetas argument

    Syntax.Case scrutinee branches maybeDefaultBranch ->
      termMetas scrutinee <>
      case branches of
        Syntax.LiteralBranches literalBranches ->
          foldMap (foldMap termMetas) literalBranches

        Syntax.ConstructorBranches _constructorTypeName constructorBranches ->
          foldMap (foldMap telescopeMetas) constructorBranches

      <>
      foldMap termMetas maybeDefaultBranch

    Syntax.Spanned _span term' ->
      termMetas term'

telescopeMetas :: Telescope binding Syntax.Type Syntax.Term v -> IntSet Meta.Index
telescopeMetas tele =
  case tele of
    Telescope.Empty term ->
      termMetas term

    Telescope.Extend _binding type_ _plixity tele' ->
      termMetas type_ <> telescopeMetas tele'
