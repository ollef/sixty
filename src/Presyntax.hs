{-# language DeriveGeneric #-}
{-# language DeriveAnyClass #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
module Presyntax where

import Protolude hiding (Type)

import qualified Name

newtype Name = Name Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, IsString)

data Term
  = Var !Name
  | Let !Name.Name !Term !Term
  | Pi !Name.Name !Type !Type
  | Fun !Type !Type
  | Lam !Name.Name !Term
  | App !Term !Term
  deriving (Show, Generic, Hashable)

type Type = Term

apps :: Foldable f => Term -> f Term -> Term
apps = foldl App

data Definition
  = TypeDeclaration !Name.Name !Type
  | ConstantDefinition !Name.Name !Term
  deriving (Show, Generic, Hashable)

definitionName :: Definition -> Name.Name
definitionName def =
  case def of
    TypeDeclaration name _ -> name
    ConstantDefinition name _ -> name
