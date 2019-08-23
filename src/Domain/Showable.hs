{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language PackageImports #-}
module Domain.Showable where

import Protolude hiding (Type, IntMap, force, to)

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
  | Glued !Domain.Head Spine !Value
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
  Branches :: Environment v -> Syntax.Branches v -> Maybe (Syntax.Term v) -> Branches

deriving instance Show Branches

to :: Domain.Value -> M Value
to value =
  case value of
    Domain.Neutral hd spine ->
      Neutral hd <$> mapM (mapM to) spine

    Domain.Glued hd spine value' ->
      Glued hd <$> mapM (mapM to) spine <*> lazyTo value'

    Domain.Lam name type_ plicity closure ->
      Lam name <$> to type_ <*> pure plicity <*> closureTo closure

    Domain.Pi name type_ plicity closure ->
      Pi name <$> to type_ <*> pure plicity <*> closureTo closure

    Domain.Fun source domain ->
      Fun <$> to source <*> to domain

    Domain.Case scrutinee branches ->
      Case <$> to scrutinee <*> branchesTo branches

lazyTo :: Lazy Domain.Value -> M Value
lazyTo =
  to <=< force

closureTo :: Domain.Closure -> M Closure
closureTo (Domain.Closure env term) =
  flip Closure term <$> environmentTo env

branchesTo :: Domain.Branches -> M Branches
branchesTo (Domain.Branches env branches defaultBranch) = do
  env' <- environmentTo env
  pure $ Branches env' branches defaultBranch

environmentTo :: Domain.Environment v -> M (Environment v)
environmentTo env = do
  values' <- mapM to $ Domain.values env
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
