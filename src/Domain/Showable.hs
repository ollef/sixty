{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language PackageImports #-}
module Domain.Showable where

import Protolude hiding (Type, IntMap, force)

import "this" Data.IntMap (IntMap)
import Data.Tsil (Tsil)
import qualified Domain
import Index
import qualified Index.Map as Index
import Monad
import Name (Name)
import Plicity
import qualified Scope
import qualified Syntax
import Var

data Value
  = Neutral !Domain.Head Spine
  | Lam !Name !Type !Plicity !Closure
  | Pi !Name !Type !Plicity !Closure
  | Fun !Type !Type
  | Case !Value !Branches
  deriving Show

type Type = Value

type Spine = Tsil (Plicity, Value)

data Closure where
  Closure :: Environment v -> Scope Syntax.Term v -> Closure

deriving instance Show Closure

data Branches where
  Branches :: Environment v -> [Syntax.Branch v] -> Branches

deriving instance Show Branches

go :: Domain.Value -> M Value
go value =
  case value of
    Domain.Neutral hd spine ->
      Neutral hd <$> mapM (mapM goForce) spine

    Domain.Lam name type_ plicity closure ->
      Lam name <$> goForce type_ <*> pure plicity <*> goClosure closure

    Domain.Pi name type_ plicity closure ->
      Pi name <$> goForce type_ <*> pure plicity <*> goClosure closure

    Domain.Fun source domain ->
      Fun <$> goForce source <*> goForce domain

    Domain.Case scrutinee branches ->
      Case <$> go scrutinee <*> goBranches branches

goForce :: Lazy Domain.Value -> M Value
goForce = go <=< force

goClosure :: Domain.Closure -> M Closure
goClosure (Domain.Closure env term) =
  flip Closure term <$> goEnv env

goBranches :: Domain.Branches -> M Branches
goBranches (Domain.Branches env branches) =
  flip Branches branches <$> goEnv env

goEnv :: Domain.Environment v -> M (Environment v)
goEnv env = do
  values' <- mapM goForce $ Domain.values env
  pure $ Environment
    { scopeKey = Domain.scopeKey env
    , indices = Domain.indices env
    , values = values'
    }

data Environment v = Environment
  { scopeKey :: !Scope.KeyedName
  , indices :: Index.Map v Var
  , values :: IntMap Var Value
  } deriving Show
