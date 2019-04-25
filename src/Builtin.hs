{-# language OverloadedStrings #-}
module Builtin where

import qualified Domain

type_ :: Domain.Value
type_ = Domain.global "type"
