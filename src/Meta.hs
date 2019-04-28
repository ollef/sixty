{-# language GeneralizedNewtypeDeriving #-}
module Meta where

import Protolude hiding (Map)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

data Var v
  = Unsolved
  | Solved v

newtype Index = Index Int
  deriving (Eq, Ord, Show, Hashable)

data Map v = Map
  { map :: HashMap Index (Meta.Var v)
  , nextIndex :: !Index
  }

empty :: Map v
empty = Map mempty (Index 0)

lookup :: Index -> Map v -> Var v
lookup i (Map m _) = m HashMap.! i

insert :: Map v -> (Map v, Index)
insert (Map m i@(Index n)) = (Map (HashMap.insert i Unsolved m) (Index (n + 1)), i)

solve :: Index -> v -> Map v -> Map v
solve i v (Map m n) = Map (HashMap.insert i (Solved v) m) n
