{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Scope where

import Protolude

import Data.HashMap.Lazy (HashMap)

import Name (Name)
import qualified Name
import qualified Presyntax

data Key
  = Type
  | Definition
  deriving (Eq, Ord, Show, Generic, Hashable)

data KeyedName = KeyedName !Key !Name.Qualified
  deriving (Eq, Ord, Show, Generic, Hashable)

type Visibility = Key

type Scope =
  HashMap Name Visibility

type Scopes =
  HashMap (Name, Key) Scope

keyed :: Presyntax.Definition -> ((Key, Name), Presyntax.Term)
keyed def =
  case def of
    Presyntax.ConstantDefinition name term ->
      ((Definition, name), term)

    Presyntax.TypeDeclaration name type_ ->
      ((Type, name), type_)
