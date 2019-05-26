{-# language OverloadedStrings #-}
module Builtin where

import Protolude

import qualified Domain

typeName :: IsString s => s
typeName = "Builtin.Type"

type_ :: Domain.Value
type_ = Domain.global typeName

fail :: IsString s => s
fail = "Builtin.fail"
