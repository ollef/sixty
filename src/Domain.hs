{-# language GADTs #-}
module Domain where

import Protolude hiding (Type, Seq)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Index
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Sequence (Seq)
import qualified Sequence as Seq
import qualified Syntax
import Tsil (Tsil)
import qualified Tsil
import Var (Var)

data Value
  = Neutral !Head Spine
  | Lam !Name !(Lazy Type) !Closure
  | Pi !Name !(Lazy Type) !Closure
  | Fun !(Lazy Type) !(Lazy Type)

type Type = Value

data Head
  = Var !Var
  | Meta !Meta.Index
  | Global !Name.Elaborated
  deriving (Eq, Show)

type Spine = Tsil (Lazy Value)

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

var :: Var -> Value
var v = Neutral (Domain.Var v) Tsil.Nil

global :: Name.Elaborated -> Value
global g = Neutral (Global g) Tsil.Nil

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) Tsil.Nil

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Tsil.Nil) = Just v
singleVarView _ = Nothing

-------------------------------------------------------------------------------
-- Evaluation environments

data Environment v = Environment
  { vars :: Seq Var
  , values :: HashMap Var (Lazy Domain.Value)
  }

empty :: Environment Void
empty =
  Environment
    { vars = mempty
    , values = mempty
    }

extend
  :: Environment v
  -> M (Environment (Succ v))
extend env = do
  v <- freshVar
  pure env
    { vars = vars env Seq.:> v
    }

extendValue
  :: Environment v
  -> Lazy Domain.Value
  -> M (Environment (Succ v))
extendValue env value = do
  v <- freshVar
  pure env
    { vars = vars env Seq.:> v
    , values = HashMap.insert v value (values env)
    }

lookupValue :: Index v -> Environment v -> Lazy Domain.Value
lookupValue (Index i) env =
  let
    v = Seq.index (vars env) (Seq.length (vars env) - i - 1)
  in
  fromMaybe
    (Lazy $ pure $ var v)
    (HashMap.lookup v $ values env)
