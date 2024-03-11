{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Core.Environment where

import qualified Core.Domain as Domain
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import Data.IORef
import qualified Data.Kind
import qualified Elaboration.Meta as Meta
import Index
import qualified Index.Map
import qualified Index.Map as Index (Map)
import Literal (Literal)
import Monad
import qualified Name
import Protolude
import Var (Var)

data Environment (v :: Data.Kind.Type) = Environment
  { indices :: Index.Map v Var
  , equal :: HashMap Domain.Head [(Domain.Spine, Domain.Value)]
  , notEqual :: HashMap Domain.Head [(Domain.Spine, HashSet Name.QualifiedConstructor, HashSet Literal)]
  , glueableBefore :: !(Index (Succ v))
  }

empty :: Environment Void
empty =
  Environment
    { indices = Index.Map.Empty
    , equal = mempty
    , notEqual = mempty
    , glueableBefore = Index.Zero
    }

extend
  :: Environment v
  -> M (Environment (Succ v), Var)
extend env = do
  var <- freshVar
  pure (extendVar env var, var)

extendVar
  :: Environment v
  -> Var
  -> Environment (Succ v)
extendVar env v =
  env
    { indices = env.indices Index.Map.:> v
    , glueableBefore = Index.Succ env.glueableBefore
    }

extendValue
  :: Environment v
  -> Domain.Value
  -> M (Environment (Succ v), Var)
extendValue env value = do
  var <- freshVar
  pure
    ( env
        { indices = env.indices Index.Map.:> var
        , equal = HashMap.insert (Domain.Var var) [(mempty, value)] env.equal
        , glueableBefore = Index.Succ env.glueableBefore
        }
    , var
    )

define :: Environment v -> Domain.Head -> Domain.Spine -> Domain.Value -> Environment v
define env head_ spine value =
  env {equal = HashMap.insertWith (<>) head_ [(spine, value)] env.equal}

lookupVarIndex :: Var -> Environment v -> Maybe (Index v)
lookupVarIndex var env =
  Index.Map.elemIndex var env.indices

lookupIndexVar :: Index v -> Environment v -> Var
lookupIndexVar index env =
  Index.Map.index (indices env) index

lookupIndexValue :: Index v -> Environment v -> Maybe Domain.Value
lookupIndexValue index env =
  lookupVarValue (lookupIndexVar index env) env

lookupVarValue :: Var -> Environment v -> Maybe Domain.Value
lookupVarValue v env =
  case HashMap.lookup (Domain.Var v) env.equal of
    Just [(Domain.Empty, value)] -> Just value
    _ -> Nothing
