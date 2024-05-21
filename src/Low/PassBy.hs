{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Low.PassBy where

import Low.Representation (Representation)
import Prettyprinter
import Protolude hiding (repr)

data PassBy
  = Value !Representation
  | Reference
  deriving (Eq, Show, Generic, Hashable)

instance Pretty PassBy where
  pretty = \case
    Value repr -> pretty repr
    Reference -> "ref"
