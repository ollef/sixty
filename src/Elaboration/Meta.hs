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
import Protolude hiding (IntMap, IntSet, State, state, link, link2)
import qualified Span
import Telescope (Telescope)
import qualified Telescope

data Entry m
  = Unsolved !Link (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | Solved !Link (Syntax.Term Void) (Syntax.Type Void)
  | LazilySolved !Link !(m (Syntax.Term Void)) (Syntax.Type Void)

entryLink :: Entry m -> Link
entryLink entry =
  case entry of
    Unsolved l _ _ _ _ ->
      l

    Solved l _ _ ->
      l

    LazilySolved l _ _ ->
      l

entryWeight :: Entry m -> Double
entryWeight =
  weight . entryLink

entryType :: Entry m -> Syntax.Type Void
entryType entry =
  case entry of
    Unsolved _ type_ _ _ _ ->
      type_

    Solved _ _ type_ ->
      type_

    LazilySolved _ _ type_ ->
      type_

mapEntryLink :: (Link -> Link) -> Entry m -> Entry m
mapEntryLink f entry =
  case entry of
    Unsolved l a b c d ->
      Unsolved (f l) a b c d

    Solved l a b ->
      Solved (f l) a b

    LazilySolved l a b ->
      LazilySolved (f l) a b

data State m = State
  { entries :: IntMap Meta.Index (Entry m) -- invariant: weights <= greatestMeta < nextIndex
  , nextIndex :: !Meta.Index
  , greatest :: Maybe Meta.Index
  }

data Link = Link
  { previous :: Maybe Meta.Index
  , weight :: !Double
  , next :: Maybe Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

empty :: State m
empty =
  State
    { entries = mempty
    , nextIndex = Meta.Index 0
    , greatest = Nothing
    }

lookup :: Meta.Index -> State m -> Entry m
lookup index state =
  entries state IntMap.! index

new :: Syntax.Term Void -> Int -> Span.Relative -> State m -> (State m, Meta.Index)
new type_ arity span state =
  let
    index@(Meta.Index indexInt) =
      nextIndex state

    link =
      Link
        { previous = greatest state
        , weight = fromIntegral indexInt
        , next = Nothing
        }
  in
  ( State
    { entries = IntMap.insert index (Unsolved link type_ arity mempty span) $ entries state
    , nextIndex = nextIndex state + 1
    , greatest = Just index
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

        Just (Unsolved link type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ Solved link term type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

        Just LazilySolved {} ->
          panic "Solving an already solved meta variable"

lazilySolve :: Meta.Index -> m (Syntax.Term Void) -> State m -> (State m, (Int, IntSet Postponement.Index))
lazilySolve index mterm state =
  (state { entries = entries' }, data_)
  where
    (data_, entries') =
      IntMap.alterF alter index $ entries state

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved link type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ LazilySolved link mterm type_)

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
        Unsolved link type_ arity postponed span ->
          Unsolved link type_ arity (IntSet.insert postponementIndex postponed) span

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
        Unsolved link type_ arity postponed span ->
          Unsolved link type_ arity (postponementIndices <> postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"

        LazilySolved {} ->
          panic "Adding postponement index to an already solved meta variable"

-------------------------------------------------------------------------------
-- Weights

-- | `moveBefore m1 m2` moves m2 just before m1 in the state.
moveBefore :: Meta.Index -> Meta.Index -> State m -> State m
moveBefore index1 index2 state
  | previousWeight < newWeight2
  , newWeight2 < weight link1 =
    state
      { entries =
        mapMaybeLink (previous link1) (\link -> link { next = Just index2 }) $
        mapLink index2 (const Link { previous = previous link1, weight = newWeight2, next = Just index1 }) $
        mapLink index1 (\link -> link { previous = Just index2 }) $
        mapMaybeLink (previous link2) (\link -> link { next = next link2 }) $
        mapMaybeLink (next link2) (\link -> link { previous = previous link2 }) $
        entries state
      , greatest =
        if Just index2 == greatest state then
          previous link2
        else
          greatest state
      }
  | otherwise =
    moveBefore index1 index2 $ reassignWeights state
  where
    entry1 =
      lookup index1 state

    entry2 =
      lookup index2 state

    link1 =
      entryLink entry1

    link2 =
      entryLink entry2

    previousWeight =
      case previous link1 of
        Nothing ->
          -1

        Just prev ->
          weight $ entryLink $ lookup prev state

    newWeight2 =
      (previousWeight + weight link1) / 2

    mapMaybeLink :: Maybe Meta.Index -> (Link -> Link) -> IntMap Meta.Index (Entry m) -> IntMap Meta.Index (Entry m)
    mapMaybeLink maybeIndex f =
      maybe identity (`mapLink` f) maybeIndex

    mapLink :: Meta.Index -> (Link -> Link) -> IntMap Meta.Index (Entry m) -> IntMap Meta.Index (Entry m)
    mapLink index f =
      IntMap.adjust (mapEntryLink f) index

reassignWeights :: State m -> State m
reassignWeights state =
  state
    { entries =
      IntMap.fromList $
      zipWith (\newWeight (index, entry) -> (index, mapEntryLink (\link -> link { weight = newWeight }) entry)) [0..] $
      sortOn (weight . entryLink . snd) $
      IntMap.toList $
      entries state
    }

-------------------------------------------------------------------------------
-- Eager entries

data EagerEntry
  = EagerUnsolved !Link (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | EagerSolved !Link (Syntax.Term Void) (Syntax.Type Void)
  deriving (Eq, Generic, Persist, Hashable)

data EagerState = EagerState
  { eagerEntries :: IntMap Meta.Index EagerEntry
  , eagerNextIndex :: !Meta.Index
  , eagerGreatest :: Maybe Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

fromEagerState :: EagerState -> State m
fromEagerState state =
  State
    { entries = fromEagerEntry <$> eagerEntries state
    , nextIndex = eagerNextIndex state
    , greatest = eagerGreatest state
    }

fromEagerEntry :: EagerEntry -> Entry m
fromEagerEntry entry =
  case entry of
    EagerUnsolved link type_ arity postponements span ->
      Unsolved link type_ arity postponements span

    EagerSolved link term type_ ->
      Solved link term type_

toEagerEntry :: Monad m => Entry m -> m EagerEntry
toEagerEntry entry =
  case entry of
    Unsolved link type_ arity postponements span ->
      pure $ EagerUnsolved link type_ arity postponements span

    Solved link solution type_ ->
      pure $ EagerSolved link solution type_

    LazilySolved link msolution type_ -> do
      solution <- msolution
      pure $ EagerSolved link solution type_

toEagerState :: Monad m => State m -> Syntax.Definition -> Maybe (Syntax.Type Void) -> m EagerState
toEagerState state definition maybeType = do
  entries_ <- go (definitionMetas definition <> foldMap termMetas maybeType) mempty
  pure EagerState
    { eagerEntries = entries_
    , eagerNextIndex = nextIndex state
    , eagerGreatest = greatest state
    }
  where
    go todo done
      | IntMap.null todo' =
        pure done

      | otherwise = do
        newlyDone <-
          traverse
            (\case
              Unsolved link type_ arity postponements span ->
                pure $ EagerUnsolved link type_ arity postponements span

              Solved link solution type_ ->
                pure $ EagerSolved link solution type_

              LazilySolved link msolution type_ -> do
                solution <- msolution
                pure $ EagerSolved link solution type_
            )
            todo'

        let
          newTodo =
            foldMap
              (\case
                EagerUnsolved _link type_ _arity _postponements _span ->
                  termMetas type_

                EagerSolved _link solution _ ->
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
