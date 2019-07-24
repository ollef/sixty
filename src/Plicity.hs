{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE OverloadedStrings #-}
module Plicity where

import Protolude

import Data.Text.Prettyprint.Doc

data Plicity
  = Implicit
  | Explicit
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Pretty Plicity where
  pretty plicity =
    case plicity of
      Implicit ->
        "implicit"

      Explicit ->
        "explicit"

prettyAnnotation :: Plicity -> Doc ann
prettyAnnotation plicity =
  case plicity of
    Implicit ->
      "@"

    Explicit ->
      ""

implicitise :: Plicity -> Plicity
implicitise _ =
  Implicit
