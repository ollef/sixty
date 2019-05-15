module Presyntax where

import Protolude hiding (Type)

import Name (Name)

data Term
  = Var !Name
  | Let !Name !Term !Term
  | Pi !Name !Type !Type
  | Fun !Type !Type
  | Lam !Name !Term
  | App !Term !Term
  deriving Show

type Type = Term

apps :: Foldable f => Term -> f Term -> Term
apps = foldl App
