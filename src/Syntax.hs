{-# language GADTs #-}
module Syntax where

import Protolude

import Bound.Var
import Bound.Scope.Simple

data Term v
  = Var !v
  | Global !Text
  | Let (Term v) (Scope () Term v)
  | Pi (Term v) (Scope () Term v)
  | Lam (Scope () Term v)
  | App (Term v) (Term v)

type Type = Term

data Env val v where
  Nil :: Env val Void
  Snoc :: Env val v -> val -> Env val (Var () v)

lookupValue :: Env val v -> v -> val
lookupValue Nil v = absurd v
lookupValue (Snoc _ val) (B ~()) = val
lookupValue (Snoc env _) (F v) = lookupValue env v

lookupIndex
  :: Env val v
  -> (val -> Bool)
  -> Maybe (v, val)
lookupIndex Nil _ = Nothing
lookupIndex (Snoc env val) p
  | p val = Just (B (), val)
  | otherwise = first F <$> lookupIndex env p
