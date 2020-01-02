{-# language OverloadedStrings #-}
{-# language DuplicateRecordFields #-}
module ClosureConverted.Context where

import Protolude hiding (IntMap)

import qualified ClosureConverted.Domain as Domain
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Environment (Environment(Environment))
import qualified Environment
import Index
import qualified Index.Map
import qualified Index.Map as Index
import Monad
import qualified Scope
import Var (Var)
import qualified Var

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , indices :: Index.Map v Var
  , values :: IntMap Var Domain.Value
  , types :: IntMap Var Domain.Type
  }

empty :: Scope.KeyedName -> Context Void
empty scopeKey_ =
  Context
    { scopeKey = scopeKey_
    , indices = Index.Map.Empty
    , values = mempty
    , types = mempty
    }

lookupVarType :: Var -> Context v -> Domain.Type
lookupVarType var context =
  fromMaybe (panic "Context.lookupVarType")
    $ IntMap.lookup var
    $ types context

toEnvironment
  :: Context v
  -> Domain.Environment v
toEnvironment context =
  Environment
    { scopeKey = scopeKey context
    , indices = indices context
    , values = values context
    }

extend
  :: Context v
  -> Domain.Type
  -> M (Context (Succ v), Var)
extend context type_ = do
  var <- freshVar
  pure
    ( context
      { indices = indices context Index.Map.:> var
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )
