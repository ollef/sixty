{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
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
import Protolude hiding (IntMap, IntSet, State)
import qualified Span

data Entry
  = Unsolved (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | Solved (Syntax.Term Void) (Syntax.Type Void)
  deriving (Eq, Generic, Persist, Hashable)

data State = State
  { entries :: !(IntMap Meta.Index Entry)
  , nextIndex :: !Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

empty :: State
empty =
  State mempty $ Meta.Index 0

lookup :: Meta.Index -> State -> Entry
lookup index (State m _) =
  m IntMap.! index

insert :: Syntax.Term Void -> Int -> Span.Relative -> State -> (State, Meta.Index)
insert type_ arity span (State m index) =
  (State (IntMap.insert index (Unsolved type_ arity mempty span) m) (index + 1), index)

solve :: Meta.Index -> Syntax.Term Void -> State -> (State, (Int, IntSet Postponement.Index))
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

addPostponedIndex :: Meta.Index -> Postponement.Index -> State -> State
addPostponedIndex index postponementIndex (State m n) =
  State (IntMap.adjust adjust index m) n
  where
    adjust entry =
      case entry of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (IntSet.insert postponementIndex postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"

addPostponedIndices :: Meta.Index -> IntSet Postponement.Index -> State -> State
addPostponedIndices index postponementIndices (State m n) =
  State (IntMap.adjust adjust index m) n
  where
    adjust entry =
      case entry of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (postponementIndices <> postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"
