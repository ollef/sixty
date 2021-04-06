{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Plicity where

import Data.Persist
import Data.Text.Prettyprint.Doc
import Protolude

data Plicity
  = Implicit
  | Explicit
  | Constraint
  deriving (Eq, Ord, Show, Generic, Persist, Hashable)

instance Pretty Plicity where
  pretty plicity =
    case plicity of
      Implicit ->
        "implicit"
      Explicit ->
        "explicit"
      Constraint ->
        "constraint"

isImplicitish :: Plicity -> Bool
isImplicitish plicity =
  case plicity of
    Implicit ->
      True
    Explicit ->
      False
    Constraint ->
      True

prettyAnnotation :: Plicity -> Doc ann
prettyAnnotation plicity =
  case plicity of
    Implicit ->
      "@"
    Explicit ->
      ""
    Constraint ->
      "!"

implicitise :: Plicity -> Plicity
implicitise plicity =
  case plicity of
    Explicit ->
      Implicit
    Implicit ->
      Implicit
    Constraint ->
      Constraint
