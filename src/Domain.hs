{-# language GADTs #-}
{-# language PackageImports #-}
module Domain where

import Protolude hiding (Type, Seq, IntMap)

import "this" Data.IntMap (IntMap)
import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import qualified "this" Data.IntMap as IntMap
import qualified Scope
import qualified Syntax
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
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Meta !Meta.Index
  deriving (Eq, Show)

type Spine = Tsil (Lazy Value)

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

var :: Var -> Value
var v = Neutral (Domain.Var v) mempty

global :: Name.Qualified -> Value
global g = Neutral (Global g) mempty

con :: Name.QualifiedConstructor -> Value
con c = Neutral (Con c) mempty

meta :: Meta.Index -> Value
meta i = Neutral (Meta i) mempty

singleVarView :: Value -> Maybe Var
singleVarView (Neutral (Var v) Tsil.Empty) = Just v
singleVarView _ = Nothing

-------------------------------------------------------------------------------
-- Evaluation environments

data Environment v = Environment
  { scopeKey :: !Scope.KeyedName
  , vars :: IntSeq Var
  , values :: IntMap Var (Lazy Domain.Value)
  }

empty :: Scope.KeyedName -> Environment Void
empty key =
  Environment
    { scopeKey = key
    , vars = mempty
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
