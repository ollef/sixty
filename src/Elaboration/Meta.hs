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
import Data.List (partition)
import Data.Persist
import qualified Meta
import Orphans ()
import qualified Postponement
import Protolude hiding (IntMap, IntSet, State, state, link, link2)
import qualified Span
import Telescope (Telescope)
import qualified Telescope

data Entry m
  = Unsolved (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | Solved (Syntax.Term Void) !CachedMetas (Syntax.Type Void)
  | LazilySolved !(m (Syntax.Term Void)) !(m (IntSet Meta.Index)) (Syntax.Type Void)

data CachedMetas = CachedMetas
  { direct :: IntSet Meta.Index
  , unsolved :: IntSet Meta.Index -- Or unknown
  , solved :: IntSet Meta.Index
  } deriving (Eq, Show, Generic, Persist, Hashable)

instance Semigroup CachedMetas where
  CachedMetas a1 b1 c1 <> CachedMetas a2 b2 c2 =
    CachedMetas (a1 <> a2) (b1 <> b2) (c1 <> c2)

instance Monoid CachedMetas where
  mempty = CachedMetas mempty mempty mempty

entryType :: Entry m -> Syntax.Type Void
entryType entry =
  case entry of
    Unsolved type_ _ _ _ ->
      type_

    Solved _ _ type_ ->
      type_

    LazilySolved _ _ type_ ->
      type_

data State m = State
  { entries :: IntMap Meta.Index (Entry m)
  , nextIndex :: !Meta.Index
  }

empty :: State m
empty =
  State
    { entries = mempty
    , nextIndex = Meta.Index 0
    }

lookup :: Meta.Index -> State m -> Entry m
lookup index state =
  entries state IntMap.! index

new :: Syntax.Term Void -> Int -> Span.Relative -> State m -> (State m, Meta.Index)
new type_ arity span state =
  let
    index =
      nextIndex state
  in
  ( State
    { entries = IntMap.insert index (Unsolved type_ arity mempty span) $ entries state
    , nextIndex = nextIndex state + 1
    }
  , index
  )

solve :: Meta.Index -> Syntax.Term Void -> State m -> (State m, (Int, IntSet Postponement.Index))
solve index term state =
  (state { entries = entries' }, data_)
  where
    (data_, entries') =
      IntMap.alterF alter index $ entries state

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved type_ arity' postponed' _) -> do
          let
            metas =
              termMetas term <> termMetas type_
          ((arity', postponed'), Just $ Solved term mempty { direct = metas, unsolved = metas } type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

        Just LazilySolved {} ->
          panic "Solving an already solved meta variable"

lazilySolve :: Functor m => Meta.Index -> m (Syntax.Term Void) -> State m -> (State m, (Int, IntSet Postponement.Index))
lazilySolve index mterm state =
  (state { entries = entries' }, data_)
  where
    (data_, entries') =
      IntMap.alterF alter index $ entries state

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ LazilySolved mterm (termMetas <$> mterm) type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

        Just LazilySolved {} ->
          panic "Solving an already solved meta variable"

addPostponedIndex :: Meta.Index -> Postponement.Index -> State m -> State m
addPostponedIndex index postponementIndex state =
  state { entries = IntMap.adjust adjust index $ entries state }
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
addPostponedIndices index postponementIndices state =
  state { entries = IntMap.adjust adjust index $ entries state }
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
  | EagerSolved (Syntax.Term Void) CachedMetas (Syntax.Type Void)
  deriving (Eq, Generic, Persist, Hashable)

data EagerState = EagerState
  { eagerEntries :: IntMap Meta.Index EagerEntry
  , eagerNextIndex :: !Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

fromEagerState :: EagerState -> State m
fromEagerState state =
  State
    { entries = fromEagerEntry <$> eagerEntries state
    , nextIndex = eagerNextIndex state
    }

fromEagerEntry :: EagerEntry -> Entry m
fromEagerEntry entry =
  case entry of
    EagerUnsolved type_ arity postponements span ->
      Unsolved type_ arity postponements span

    EagerSolved term metas type_ ->
      Solved term metas type_

toEagerEntry :: Monad m => Entry m -> m EagerEntry
toEagerEntry entry =
  case entry of
    Unsolved type_ arity postponements span ->
      pure $ EagerUnsolved type_ arity postponements span

    Solved solution metas type_ ->
      pure $ EagerSolved solution metas type_

    LazilySolved msolution mmetas type_ -> do
      solution <- msolution
      metas <- mmetas
      pure $ EagerSolved solution mempty { direct = metas, unsolved = metas } type_

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
        newlyDone <- traverse toEagerEntry todo'

        let
          newTodo =
            foldMap
              (\case
                EagerUnsolved type_ _arity _postponements _span ->
                  termMetas type_

                EagerSolved _solution metas _type ->
                  direct metas
              )
              newlyDone

        go newTodo (done <> newlyDone)
      where
        todo' =
          IntMap.difference (IntMap.fromSet (entries state IntMap.!) todo) done

-------------------------------------------------------------------------------

solutionMetas :: Monad m => Meta.Index -> State m -> m (Maybe CachedMetas, State m)
solutionMetas metaIndex state = do
  case lookup metaIndex state of
    Unsolved {} ->
      pure (Nothing, state)

    Solved solution metas type_ ->
      flip runStateT state $ do
        indirects <- forM (IntSet.toList $ unsolved metas) $ \i ->
          (,) i <$> StateT (solutionMetas i)

        let
          (directUnsolvedMetas, directSolvedMetas) =
            bimap (IntSet.fromList . map fst) (IntSet.fromList . map fst) $
            partition (isNothing . snd) indirects

          indirectMetas =
            foldMap (fold . snd) indirects

          solved' =
            solved metas <> directSolvedMetas <> solved indirectMetas

          unsolved' =
            directUnsolvedMetas <> unsolved indirectMetas

          metas' =
            metas
              { unsolved = unsolved'
              , solved = solved'
              }

        modify $ \s -> s { entries = IntMap.insert metaIndex (Solved solution metas' type_) $ entries s }

        pure (Just metas')

    LazilySolved msolution mmetas type_ -> do
      solution <- msolution
      metas <- mmetas
      solutionMetas metaIndex state
        { entries =
          IntMap.insert metaIndex (Solved solution CachedMetas { direct = metas, unsolved = metas, solved = mempty } type_) $ entries state
        }

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
