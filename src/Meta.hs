{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Meta where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

data Var term
  = Unsolved term
  | Solved term term

newtype Index = Index Int
  deriving (Eq, Ord, Show, Hashable)

data Vars term = Vars
  { vars :: !(HashMap Index (Var term))
  , nextIndex :: !Index
  }

empty :: Vars term
empty = Vars mempty (Index 0)

lookup :: Index -> Vars term -> Var term
lookup index (Vars m _) = m HashMap.! index

insert :: term -> Vars term -> (Vars term, Index)
insert unsolved (Vars m index@(Index n)) = (Vars (HashMap.insert index (Unsolved unsolved) m) (Index (n + 1)), index)

solve :: Index -> term -> Vars term -> Vars term
solve index term (Vars m n) = Vars (HashMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved typ ->
          Solved term typ

        Solved _ _ ->
          panic "Solving an already solved meta variable"
