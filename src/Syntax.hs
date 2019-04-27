{-# language GADTs #-}
module Syntax where

import Protolude

import Bound.Var
import Bound.Scope.Simple
import Index

data Term v
  = Var !(Index v)
  | Global !Text
  | Let (Term v) (Scope () Term v)
  | Pi (Term v) (Scope () Term v)
  | Fun (Term v) (Term v)
  | Lam (Scope () Term v)
  | App (Term v) (Term v)

type Type = Term

data Env val v where
  Nil :: Env val Void
  Snoc :: Env val v -> val -> Env val (Var () v)

lookupValue :: Env val v -> Index v -> val
lookupValue Nil v = absurdIndex v
lookupValue (Snoc _ val) Zero = val
lookupValue (Snoc env _) (Succ v) = lookupValue env v

lookupIndex
  :: Env val v
  -> (val -> Bool)
  -> Maybe (Index v, val)
lookupIndex Nil _ = Nothing
lookupIndex (Snoc env val) p
  | p val = Just (Zero, val)
  | otherwise = first Succ <$> lookupIndex env p
