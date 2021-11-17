{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module ClosureConverted.Context where

import qualified ClosureConverted.Domain as Domain
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Environment (Environment (Environment))
import qualified Environment
import Index
import qualified Index.Map
import qualified Index.Map as Index
import Monad
import Protolude hiding (IntMap, empty)
import Var (Var)
import qualified Var

data Context v = Context
  { indices :: Index.Map v Var
  , values :: IntMap Var Domain.Value
  , types :: IntMap Var Domain.Type
  , glueableBefore :: !(Index (Succ v))
  }

empty :: Context Void
empty =
  Context
    { indices = Index.Map.Empty
    , values = mempty
    , types = mempty
    , glueableBefore = Index.Zero
    }

lookupIndexVar :: Index v -> Context v -> Var
lookupIndexVar index context =
  Index.Map.index (indices context) index

lookupVarType :: Var -> Context v -> Domain.Type
lookupVarType var context =
  fromMaybe (panic $ "ClosureConverted.Context.lookupVarType " <> show var) $
    IntMap.lookup var $
      types context

toEnvironment ::
  Context v ->
  Domain.Environment v
toEnvironment context =
  Environment
    { indices = indices context
    , values = values context
    , glueableBefore = glueableBefore context
    }

extend ::
  Context v ->
  Domain.Type ->
  M (Context (Succ v), Var)
extend context type_ = do
  var <- freshVar
  pure
    ( context
        { indices = indices context Index.Map.:> var
        , types = IntMap.insert var type_ (types context)
        , glueableBefore = Index.Succ $ glueableBefore context
        }
    , var
    )
