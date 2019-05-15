{-# language GADTs #-}
module Domain where

import Protolude hiding (Type)

import qualified Meta
import Monad
import Tsil (Tsil)
import qualified Tsil
import Var (Var)
import Name (Name)
import qualified Name

data Value
  = Neutral !Head Spine
  | Lam !Name !(Lazy Type) !Closure
  | Pi !Name !(Lazy Type) !Closure
  | Fun !(Lazy Type) !(Lazy Type)

type Type = Value

data Head
  = Var !Var
  | Meta !Meta.Index
  | Global !Name.Qualified
  deriving Eq

type Spine = Tsil (Lazy Value)

newtype Closure = Closure (Lazy Value -> M Value)

var :: Var -> Value
var v = Neutral (Domain.Var v) Tsil.Nil

global :: Name.Qualified -> Value
global g = Neutral (Global g) Tsil.Nil

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) Tsil.Nil

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Tsil.Nil) = Just v
singleVarView _ = Nothing
