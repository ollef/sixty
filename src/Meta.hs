{-# language GeneralizedNewtypeDeriving #-}
module Meta where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

data Var v
  = Unsolved
  | Solved v

newtype Index = Index Int
  deriving (Eq, Ord, Show, Hashable)

data Vars v = Vars
  { vars :: !(HashMap Index (Meta.Var v))
  , nextIndex :: !Index
  }

empty :: Vars v
empty = Vars mempty (Index 0)

lookup :: Index -> Vars v -> Var v
lookup i (Vars m _) = m HashMap.! i

insert :: Vars v -> (Vars v, Index)
insert (Vars m i@(Index n)) = (Vars (HashMap.insert i Unsolved m) (Index (n + 1)), i)

solve :: Index -> v -> Vars v -> Vars v
solve i v (Vars m n) = Vars (HashMap.insert i (Solved v) m) n
