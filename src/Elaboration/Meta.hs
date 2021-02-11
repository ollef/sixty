{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module Elaboration.Meta where

import qualified Core.Syntax as Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Persist
import qualified Meta
import Orphans ()
import Protolude hiding (IntMap)
import qualified Span

data Var
  = Unsolved (Syntax.Type Void) !Span.Relative
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

insert :: Syntax.Term Void -> Span.Relative -> Vars -> (Vars, Meta.Index)
insert unsolved span (Vars m index) =
  (Vars (IntMap.insert index (Unsolved unsolved span) m) (index + 1), index)

solve :: Meta.Index -> Syntax.Term Void -> Vars -> Vars
solve index term (Vars m n) =
  Vars (IntMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved typ _ ->
          Solved term typ

        Solved _ _ ->
          panic "Solving an already solved meta variable"
