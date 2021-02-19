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
import Protolude hiding (IntMap, IntSet)
import qualified Span

data Var
  = Unsolved (Syntax.Type Void) !Int (IntSet Postponement.Index) !Span.Relative
  | Solved (Syntax.Term Void) (Syntax.Type Void)
  deriving (Eq, Generic, Persist, Hashable)

data Vars = Vars
  { vars :: !(IntMap Meta.Index Var)
  , nextIndex :: !Meta.Index
  } deriving (Eq, Generic, Persist, Hashable)

empty :: Vars
empty =
  Vars mempty (Meta.Index 0)

lookup :: Meta.Index -> Vars -> Var
lookup index (Vars m _) =
  m IntMap.! index

insert :: Syntax.Term Void -> Int -> Span.Relative -> Vars -> (Vars, Meta.Index)
insert type_ arity span (Vars m index) =
  (Vars (IntMap.insert index (Unsolved type_ arity mempty span) m) (index + 1), index)

solve :: Meta.Index -> Syntax.Term Void -> Vars -> (Vars, (Int, IntSet Postponement.Index))
solve index term (Vars m n) =
  (Vars vars' n, data_)
  where
    (data_, vars') =
      IntMap.alterF alter index m

    alter maybeVar =
      case maybeVar of
        Nothing ->
          panic "Solving non-existent meta variable"

        Just (Unsolved type_ arity' postponed' _) ->
          ((arity', postponed'), Just $ Solved term type_)

        Just Solved {} ->
          panic "Solving an already solved meta variable"

addPostponedIndex :: Meta.Index -> Postponement.Index -> Vars -> Vars
addPostponedIndex index postponementIndex (Vars m n) =
  Vars (IntMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (IntSet.insert postponementIndex postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"

addPostponedIndices :: Meta.Index -> IntSet Postponement.Index -> Vars -> Vars
addPostponedIndices index postponementIndices (Vars m n) =
  Vars (IntMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved type_ arity postponed span ->
          Unsolved type_ arity (postponementIndices <> postponed) span

        Solved {} ->
          panic "Adding postponement index to an already solved meta variable"
