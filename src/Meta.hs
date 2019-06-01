{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Meta where

import Protolude hiding (IntMap)

import "this" Data.IntMap (IntMap)
import qualified "this" Data.IntMap as IntMap

data Var term
  = Unsolved term
  | Solved term term

newtype Index = Index Int
  deriving (Eq, Ord, Show, Hashable)

data Vars term = Vars
  { vars :: !(IntMap Index (Var term))
  , nextIndex :: !Index
  }

empty :: Vars term
empty = Vars mempty (Index 0)

lookup :: Index -> Vars term -> Var term
lookup index (Vars m _) = m IntMap.! index

insert :: term -> Vars term -> (Vars term, Index)
insert unsolved (Vars m index@(Index n)) = (Vars (IntMap.insert index (Unsolved unsolved) m) (Index (n + 1)), index)

solve :: Index -> term -> Vars term -> Vars term
solve index term (Vars m n) = Vars (IntMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved typ ->
          Solved term typ

        Solved _ _ ->
          panic "Solving an already solved meta variable"
