{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Elaboration.Meta where

import qualified Core.Syntax as Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.OrderedHashMap as OrderedHashMap
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
  = EagerUnsolved (Syntax.Type Void) !Int !Span.Relative
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
    EagerUnsolved type_ arity span ->
      Unsolved type_ arity mempty span

    EagerSolved term type_ ->
      Solved term type_

toEagerEntry :: Monad m => Entry m -> m EagerEntry
toEagerEntry entry =
  case entry of
    Unsolved type_ arity _postponements span ->
      pure $ EagerUnsolved type_ arity span

    Solved solution type_ ->
      pure $ EagerSolved solution type_

    LazilySolved msolution type_ -> do
      solution <- msolution
      pure $ EagerSolved solution type_

toEagerState :: Monad m => State m -> Syntax.Definition -> Maybe (Syntax.Type Void) -> m EagerState
toEagerState state definition maybeType = do
  entries_ <- flip execStateT mempty $ flip runReaderT (entries state) $ do
    toEagerDefinition definition
    mapM_ toEagerTerm maybeType
  pure EagerState
    { eagerEntries = entries_
    , eagerNextIndex = nextIndex state
    }

type ToEagerT m = ReaderT (IntMap Meta.Index (Entry m)) (StateT (IntMap Meta.Index EagerEntry) m)

toEagerDefinition :: Monad m => Syntax.Definition -> ToEagerT m ()
toEagerDefinition definition =
  case definition of
    Syntax.TypeDeclaration type_ ->
      toEagerTerm type_

    Syntax.ConstantDefinition term ->
      toEagerTerm term

    Syntax.DataDefinition _boxity tele ->
      toEagerDataDefinition tele

toEagerDataDefinition :: Monad m => Telescope binding Syntax.Type Syntax.ConstructorDefinitions v -> ToEagerT m ()
toEagerDataDefinition tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constructorDefinitions) ->
      OrderedHashMap.mapMUnordered_ toEagerTerm constructorDefinitions

    Telescope.Extend _binding type_ _plixity tele' -> do
      toEagerTerm type_
      toEagerDataDefinition tele'

toEagerTerm :: Monad m => Syntax.Term v -> ToEagerT m ()
toEagerTerm term =
  case term of
    Syntax.Var _ ->
      pure ()

    Syntax.Global _ ->
      pure ()

    Syntax.Con _ ->
      pure ()

    Syntax.Lit _ ->
      pure ()

    Syntax.Meta index -> do
      maybeAlreadyDone <- gets $ IntMap.lookup index
      case maybeAlreadyDone of
        Nothing -> do
          entry <- asks (IntMap.! index)
          case entry of
            Unsolved type_ arity _postponements span -> do
              modify $ IntMap.insert index $ EagerUnsolved type_ arity span
              toEagerTerm type_

            Solved solution type_ -> do
              modify $ IntMap.insert index $ EagerSolved solution type_
              toEagerTerm solution
              toEagerTerm type_

            LazilySolved msolution type_ -> do
              solution <- lift $ lift msolution
              modify $ IntMap.insert index $ EagerSolved solution type_
              toEagerTerm solution
              toEagerTerm type_

        Just _ ->
          pure ()

    Syntax.PostponedCheck {} ->
      panic "Elaboration.Meta.toEagerTerm: PostponedCheck"

    Syntax.Let _binding term' type_ body -> do
      toEagerTerm term'
      toEagerTerm type_
      toEagerTerm body

    Syntax.Pi _binding domain _plicity target -> do
      toEagerTerm domain
      toEagerTerm target

    Syntax.Fun domain _plicity target -> do
      toEagerTerm domain
      toEagerTerm target

    Syntax.Lam _bindings type_ _plicity body -> do
      toEagerTerm type_
      toEagerTerm body

    Syntax.App function _plicity argument -> do
      toEagerTerm function
      toEagerTerm argument

    Syntax.Case scrutinee branches maybeDefaultBranch -> do
      toEagerTerm scrutinee
      case branches of
        Syntax.LiteralBranches literalBranches ->
          OrderedHashMap.mapMUnordered_ (mapM_ toEagerTerm) literalBranches

        Syntax.ConstructorBranches _constructorTypeName constructorBranches ->
          OrderedHashMap.mapMUnordered_ (mapM_ toEagerTelescope) constructorBranches

      mapM_ toEagerTerm maybeDefaultBranch

    Syntax.Spanned _span term' ->
      toEagerTerm term'

toEagerTelescope :: Monad m => Telescope binding Syntax.Type Syntax.Term v -> ToEagerT m ()
toEagerTelescope tele =
  case tele of
    Telescope.Empty term ->
      toEagerTerm term

    Telescope.Extend _binding type_ _plixity tele' -> do
      toEagerTerm type_
      toEagerTelescope tele'
