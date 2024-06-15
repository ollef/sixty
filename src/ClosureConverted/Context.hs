{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

module ClosureConverted.Context where

import qualified ClosureConverted.Domain as Domain
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import qualified Data.Kind
import Environment (Environment (Environment))
import qualified Environment
import Index (Index)
import qualified Index
import qualified Index.Map
import qualified Index.Map as Index
import Monad
import Protolude hiding (empty)
import Var (Var)

data Context (v :: Data.Kind.Type) = Context
  { indices :: Index.Map v Var
  , types :: EnumMap Var Domain.Type
  , glueableBefore :: !(Index (Index.Succ v))
  }

empty :: Context Index.Zero
empty =
  Context
    { indices = Index.Map.Empty
    , types = mempty
    , glueableBefore = Index.Zero
    }

lookupIndexVar :: Index v -> Context v -> Var
lookupIndexVar index context =
  Index.Map.index (indices context) index

lookupVarType :: Var -> Context v -> Domain.Type
lookupVarType var context =
  fromMaybe (panic $ "ClosureConverted.Context.lookupVarType " <> show var) $
    EnumMap.lookup var $
      types context

toEnvironment
  :: Context v
  -> Domain.Environment v
toEnvironment context =
  Environment
    { indices = indices context
    , values = mempty
    , glueableBefore = glueableBefore context
    }

extend
  :: Context v
  -> Domain.Type
  -> M (Context (Index.Succ v), Var)
extend context type_ = do
  var <- freshVar
  pure
    ( context
        { indices = indices context Index.Map.:> var
        , types = EnumMap.insert var type_ (types context)
        , glueableBefore = Index.Succ $ glueableBefore context
        }
    , var
    )
