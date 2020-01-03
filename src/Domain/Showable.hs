{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language StandaloneDeriving #-}
module Domain.Showable where

import Protolude hiding (Type, IntMap, force, to)

import Data.Tsil (Tsil)
import qualified Domain
import qualified Environment
import Index
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Name (Name)
import Plicity
import qualified Syntax
import Var (Var)

data Value
  = Neutral !Head Spine
  | Lit !Literal
  | Glued !Head Spine !Value
  | Lam !Name !Type !Plicity !Closure
  | Pi !Name !Type !Plicity !Closure
  | Fun !Type !Plicity !Type
  deriving Show

data Head
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Meta !Meta.Index
  | Case !Value !Branches
  deriving Show

type Type = Value

type Spine = Tsil (Plicity, Value)

type Environment = Environment.Environment Value

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
      Neutral <$> headTo hd <*> mapM (mapM to) spine

    Domain.Lit lit ->
      pure $ Lit lit

    Domain.Glued hd spine value' ->
      Glued <$> headTo hd <*> mapM (mapM to) spine <*> lazyTo value'

    Domain.Lam name type_ plicity closure ->
      Lam name <$> to type_ <*> pure plicity <*> closureTo closure

    Domain.Pi name type_ plicity closure ->
      Pi name <$> to type_ <*> pure plicity <*> closureTo closure

    Domain.Fun domain plicity target ->
      Fun <$> to domain <*> pure plicity <*> to target

headTo :: Domain.Head -> M Head
headTo hd =
  case hd of
    Domain.Var var ->
      pure $ Var var

    Domain.Global global ->
      pure $ Global global

    Domain.Con con ->
      pure $ Con con

    Domain.Meta meta ->
      pure $ Meta meta

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
  values' <- mapM to $ Environment.values env
  pure Environment.Environment
    { scopeKey = Environment.scopeKey env
    , indices = Environment.indices env
    , values = values'
    }
