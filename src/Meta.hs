{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Meta where

import Protolude hiding (IntMap)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Text.Prettyprint.Doc
import qualified Span

data Var term
  = Unsolved term Span.Relative
  | Solved term term
  deriving (Eq, Functor, Foldable, Traversable)

newtype Index = Index Int
  deriving (Eq, Ord, Show)

instance Pretty Index where
  pretty (Index i) =
    "?" <> pretty i

data Vars term = Vars
  { vars :: !(IntMap Index (Var term))
  , nextIndex :: !Index
  } deriving (Eq)

empty :: Vars term
empty = Vars mempty (Index 0)

lookup :: Index -> Vars term -> Var term
lookup index (Vars m _) = m IntMap.! index

insert :: term -> Span.Relative -> Vars term -> (Vars term, Index)
insert unsolved span (Vars m index@(Index n)) = (Vars (IntMap.insert index (Unsolved unsolved span) m) (Index (n + 1)), index)

solve :: Index -> term -> Vars term -> Vars term
solve index term (Vars m n) = Vars (IntMap.adjust adjust index m) n
  where
    adjust var =
      case var of
        Unsolved typ _ ->
          Solved term typ

        Solved _ _ ->
          panic "Solving an already solved meta variable"
