{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Core.Domain.Showable where

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Core.Syntax as Syntax
import Data.Tsil (Tsil)
import qualified Environment
import Index
import Literal (Literal)
import Monad
import qualified Name
import Plicity
import Protolude hiding (IntMap, Type, force, to)

data Value
  = Neutral !Domain.Head Spine
  | Con !Name.QualifiedConstructor (Tsil (Plicity, Value))
  | Lit !Literal
  | Glued !Domain.Head Spine !Value
  | Lazy !Value
  | Lam !Bindings !Type !Plicity !Closure
  | Pi !Binding !Type !Plicity !Closure
  | Fun !Type !Plicity !Type
  deriving (Show)

type Type = Value

type Spine = Tsil Elimination

data Elimination
  = App Plicity Value
  | Case !Branches
  deriving (Show)

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
      Neutral hd <$> Domain.mapM eliminationTo spine
    Domain.Con con args ->
      Con con <$> mapM (mapM to) args
    Domain.Lit lit ->
      pure $ Lit lit
    Domain.Glued hd spine value' ->
      Glued hd <$> Domain.mapM eliminationTo spine <*> to value'
    Domain.Lazy lazyValue ->
      Core.Domain.Showable.Lazy <$> lazyTo lazyValue
    Domain.Lam bindings type_ plicity closure ->
      Lam bindings <$> to type_ <*> pure plicity <*> closureTo closure
    Domain.Pi binding type_ plicity closure ->
      Pi binding <$> to type_ <*> pure plicity <*> closureTo closure
    Domain.Fun domain plicity target ->
      Fun <$> to domain <*> pure plicity <*> to target

eliminationTo :: Domain.Elimination -> M Elimination
eliminationTo elimination =
  case elimination of
    Domain.App plicity arg ->
      App plicity <$> to arg
    Domain.Case branches ->
      Case <$> branchesTo branches

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
  pure
    Environment.Environment
      { scopeKey = Environment.scopeKey env
      , indices = Environment.indices env
      , values = values'
      , glueableBefore = Environment.glueableBefore env
      }
