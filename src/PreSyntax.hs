module PreSyntax where

import Protolude

type Var = Text

data Term
  = Var !Var
  | Let !Var Term Term
  | Pi Var Term Term
  | Lam Var Term
  | App Term Term
