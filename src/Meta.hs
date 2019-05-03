{-# language GeneralizedNewtypeDeriving #-}
module Meta where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

data Var unsolved solved
  = Unsolved unsolved
  | Solved solved

newtype Index = Index Int
  deriving (Eq, Ord, Show, Hashable)

data Vars unsolved solved = Vars
  { vars :: !(HashMap Index (Var unsolved solved))
  , nextIndex :: !Index
  }

empty :: Vars unsolved solved
empty = Vars mempty (Index 0)

lookup :: Index -> Vars unsolved solved -> Var unsolved solved
lookup i (Vars m _) = m HashMap.! i

insert :: unsolved -> Vars unsolved solved -> (Vars unsolved solved, Index)
insert unsolved (Vars m i@(Index n)) = (Vars (HashMap.insert i (Unsolved unsolved) m) (Index (n + 1)), i)

solve :: Index -> solved -> Vars unsolved solved -> Vars unsolved solved
solve i v (Vars m n) = Vars (HashMap.insert i (Solved v) m) n
