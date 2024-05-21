{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Low.Representation where

import Prettyprinter
import Protolude hiding (repr)

data Representation = Representation
  { pointers :: !Int
  , nonPointerBytes :: !Int
  }
  deriving (Eq, Show, Generic, Hashable)

instance Semigroup Representation where
  repr1 <> repr2 =
    Representation
      { pointers = repr1.pointers + repr2.pointers
      , nonPointerBytes = repr1.nonPointerBytes + repr2.nonPointerBytes
      }

instance Monoid Representation where
  mempty = Empty

instance Pretty Representation where
  pretty = \case
    Representation {pointers = 0, nonPointerBytes = 0} -> "empty"
    Representation {pointers = 0, nonPointerBytes = np} -> "b" <> pretty np
    Representation {pointers = p, nonPointerBytes = 0} -> "p" <> pretty p
    Representation {pointers = p, nonPointerBytes = np} -> "p" <> pretty p <> "b" <> pretty np

pattern Empty :: Representation
pattern Empty = Representation {pointers = 0, nonPointerBytes = 0}

leastUpperBound :: Representation -> Representation -> Representation
leastUpperBound repr1 repr2 =
  Representation
    { pointers = max repr1.pointers repr2.pointers
    , nonPointerBytes =
        max repr1.nonPointerBytes repr2.nonPointerBytes
    }

wordBytes :: Int
wordBytes = 8

int :: Representation
int = Representation {pointers = 0, nonPointerBytes = wordBytes}

type_ :: Representation
type_ = Representation {pointers = 0, nonPointerBytes = wordBytes}

pointer :: Representation
pointer = Representation {pointers = 1, nonPointerBytes = 0}

rawFunctionPointer :: Representation
rawFunctionPointer = Representation {pointers = 0, nonPointerBytes = wordBytes}

shouldPassByReference :: Representation -> Bool
shouldPassByReference repr =
  repr.pointers * wordBytes + repr.nonPointerBytes > 2 * wordBytes
