{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language PackageImports #-}
module Domain where

import Protolude hiding (Type, Seq, IntMap)

import "this" Data.IntMap (IntMap)
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Flexibility (Flexibility)
import qualified Flexibility
import Index
import qualified Index.Map
import qualified Index.Map as Index
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified "this" Data.IntMap as IntMap
import qualified Scope
import qualified Syntax
import Var (Var)
import qualified Var

data Value
  = Neutral !Head Spine
  | Glued !Head Spine !(Lazy Value)
  | Lam !Name !(Lazy Type) !Plicity !Closure
  | Pi !Name !(Lazy Type) !Plicity !Closure
  | Fun !(Lazy Type) !(Lazy Type)
  | Case !Value !Branches

type Type = Value

data Head
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Meta !Meta.Index
  deriving (Eq, Show)

type Spine = Tsil (Plicity, Lazy Value)

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

data Branches where
  Branches :: Environment v -> [Syntax.Branch v] -> Branches

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

headFlexibility :: Head -> Flexibility
headFlexibility = \case
  Var _ ->
    Flexibility.Rigid

  Global _ ->
    Flexibility.Rigid

  Con _ ->
    Flexibility.Rigid

  Meta _ ->
    Flexibility.Flexible

-------------------------------------------------------------------------------
-- Evaluation environments

data Environment v = Environment
  { scopeKey :: !Scope.KeyedName
  , indices :: Index.Map v Var
  , values :: IntMap Var (Lazy Domain.Value)
  }

empty :: Scope.KeyedName -> Environment Void
empty key =
  Environment
    { scopeKey = key
    , indices = Index.Map.Empty
    , values = mempty
    }

extend
  :: Environment v
  -> M (Environment (Succ v))
extend env =
  extendVar env <$> freshVar

extendVar
  :: Environment v
  -> Var
  -> Environment (Succ v)
extendVar env v =
  env
    { indices = indices env Index.Map.:> v
    }

extendValue
  :: Environment v
  -> Lazy Domain.Value
  -> M (Environment (Succ v))
extendValue env value = do
  v <- freshVar
  pure env
    { indices = indices env Index.Map.:> v
    , values = IntMap.insert v value (values env)
    }

lookupVar :: Index v -> Environment v -> Var
lookupVar index env =
  Index.Map.index (indices env) index

lookupValue :: Var -> Environment v -> Lazy Domain.Value
lookupValue v env =
  fromMaybe
    (eager $ var v)
    (IntMap.lookup v $ values env)
