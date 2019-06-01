{-# language GADTs #-}
{-# language PackageImports #-}
module Domain where

import Protolude hiding (Type, Seq, IntMap)

import "this" Data.IntMap (IntMap)
import Index
import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import qualified "this" Data.IntMap as IntMap
import qualified Syntax
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Var (Var)
import qualified Var

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
  deriving (Eq, Show)

type Spine = Tsil (Lazy Value)

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

var :: Var -> Value
var v = Neutral (Domain.Var v) Tsil.Nil

global :: Name.Qualified -> Value
global g = Neutral (Global g) Tsil.Nil

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) Tsil.Nil

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Tsil.Nil) = Just v
singleVarView _ = Nothing

-------------------------------------------------------------------------------
-- Evaluation environments

data Environment v = Environment
  { vars :: IntSeq Var
  , values :: IntMap Var (Lazy Domain.Value)
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
    { vars = vars env IntSeq.:> v
    }

extendValue
  :: Environment v
  -> Lazy Domain.Value
  -> M (Environment (Succ v))
extendValue env value = do
  v <- freshVar
  pure env
    { vars = vars env IntSeq.:> v
    , values = IntMap.insert v value (values env)
    }

lookupValue :: Index v -> Environment v -> Lazy Domain.Value
lookupValue (Index i) env =
  let
    v = IntSeq.index (vars env) (IntSeq.length (vars env) - i - 1)
  in
  fromMaybe
    (Lazy $ pure $ var v)
    (IntMap.lookup v $ values env)
