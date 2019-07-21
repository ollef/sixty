{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE OverloadedStrings #-}
module Plicity where

import Protolude

import Data.Text.Prettyprint.Doc

data Plicity
  = Explicit
  | Implicit
  deriving (Eq, Show, Generic, Hashable)

instance Pretty Plicity where
  pretty plicity =
    case plicity of
      Explicit ->
        ""

      Implicit ->
        "@"

implicitise :: Plicity -> Plicity
implicitise _ =
  Implicit
