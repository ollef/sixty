{-# language GADTs #-}
{-# language LambdaCase #-}
module Domain where

import Protolude hiding (Type, Seq, IntMap)

import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import Literal (Literal)
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified Syntax
import Var (Var)

data Value
  = Neutral !Head Spine
  | Con !Name.QualifiedConstructor (Tsil (Plicity, Value))
  | Lit !Literal
  | Glued !Head Spine !(Lazy Value)
  | Lam !Name !Type !Plicity !Closure
  | Pi !Name !Type !Plicity !Closure
  | Fun !Type !Plicity !Type

type Type = Value

data Head
  = Var !Var
  | Global !Name.Qualified
  | Meta !Meta.Index
  | Case !Value !Branches

type Spine = Tsil (Plicity, Value)

type Environment = Environment.Environment Value

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

data Branches where
  Branches :: Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

var :: Var -> Value
var v = Neutral (Domain.Var v) mempty

global :: Name.Qualified -> Value
global g = Neutral (Global g) mempty

con :: Name.QualifiedConstructor -> Value
con c = Con c mempty

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) mempty

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Tsil.Empty) = Just v
singleVarView _ = Nothing

headFlexibility :: Head -> Flexibility
headFlexibility = \case
  Var _ ->
    Flexibility.Rigid

  Global _ ->
    Flexibility.Rigid

  Meta _ ->
    Flexibility.Flexible

  Case {} ->
    Flexibility.Flexible
