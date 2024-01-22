{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Elaboration.Postponed where

import qualified Core.Syntax as Syntax
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Monad
import qualified Postponement
import Protolude hiding (check)

data Check where
  Unchecked :: (Postponement.CanPostpone -> M (Syntax.Term v)) -> Check
  Checking :: Check
  Checked :: Syntax.Term v -> Check

data Checks = Checks
  { checks :: !(EnumMap Postponement.Index Check)
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
  checks p EnumMap.! index

insert :: (Postponement.CanPostpone -> M (Syntax.Term v)) -> Checks -> (Checks, Postponement.Index)
insert check p =
  (Checks (EnumMap.insert (nextIndex p) (Unchecked check) (checks p)) (nextIndex p + 1), nextIndex p)

update :: Postponement.Index -> Check -> Checks -> Checks
update index newCheck p =
  p {checks = EnumMap.insert index newCheck $ checks p}

adjustF :: (Functor f) => (Check -> f Check) -> Postponement.Index -> Checks -> f Checks
adjustF adjust index p =
  (\checks' -> p {checks = checks'}) <$> EnumMap.alterF alter index (checks p)
  where
    alter maybeCheck =
      case maybeCheck of
        Nothing ->
          panic "Elaboration.Postponement.adjustF: adjusting non-existent index"
        Just check ->
          Just <$> adjust check
