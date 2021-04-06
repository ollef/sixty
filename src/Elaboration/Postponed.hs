{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Elaboration.Postponed where

import qualified Core.Syntax as Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Monad
import qualified Postponement
import Protolude hiding (IntMap, check)

data Check where
  Unchecked :: (Postponement.CanPostpone -> M (Syntax.Term v)) -> Check
  Checking :: Check
  Checked :: Syntax.Term v -> Check

data Checks = Checks
  { checks :: !(IntMap Postponement.Index Check)
  , nextIndex :: !Postponement.Index
  }

empty :: Checks
empty =
  Checks
    { checks = mempty
    , nextIndex = 0
    }

lookup :: Postponement.Index -> Checks -> Check
lookup index p =
  checks p IntMap.! index

insert :: (Postponement.CanPostpone -> M (Syntax.Term v)) -> Checks -> (Checks, Postponement.Index)
insert check p =
  (Checks (IntMap.insert (nextIndex p) (Unchecked check) (checks p)) (nextIndex p + 1), nextIndex p)

update :: Postponement.Index -> Check -> Checks -> Checks
update index newCheck p =
  p {checks = IntMap.insert index newCheck $ checks p}

adjustF :: Functor f => (Check -> f Check) -> Postponement.Index -> Checks -> f Checks
adjustF adjust index p =
  (\checks' -> p {checks = checks'}) <$> IntMap.alterF alter index (checks p)
  where
    alter maybeCheck =
      case maybeCheck of
        Nothing ->
          panic "Elaboration.Postponement.adjustF: adjusting non-existent index"
        Just check ->
          Just <$> adjust check
