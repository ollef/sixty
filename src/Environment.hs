module Environment where

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.Kind
import Index
import qualified Index.Map
import qualified Index.Map as Index
import Monad
import Protolude
import Var (Var)

data Environment value (v :: Data.Kind.Type) = Environment
  { indices :: Index.Map v Var
  , values :: EnumMap Var value
  , glueableBefore :: !(Index (Succ v))
  }
  deriving (Show)

empty :: Environment value Void
empty =
  Environment
    { indices = Index.Map.Empty
    , values = mempty
    , glueableBefore = Index.Zero
    }

extend
  :: Environment value v
  -> M (Environment value (Succ v), Var)
extend env = do
  var <- freshVar
  pure (extendVar env var, var)

extendVar
  :: Environment value v
  -> Var
  -> Environment value (Succ v)
extendVar env v =
  env
    { indices = indices env Index.Map.:> v
    , glueableBefore = Index.Succ $ glueableBefore env
    }

extendValue
  :: Environment value v
  -> value
  -> M (Environment value (Succ v), Var)
extendValue env value = do
  var <- freshVar
  pure
    ( env
        { indices = indices env Index.Map.:> var
        , values = EnumMap.insert var value (values env)
        , glueableBefore = Index.Succ $ glueableBefore env
        }
    , var
    )

define :: Environment value v -> Var -> value -> Environment value v
define env var value =
  env {values = EnumMap.insert var value (values env)}

lookupVarIndex :: Var -> Environment value v -> Maybe (Index v)
lookupVarIndex var context =
  Index.Map.elemIndex var (indices context)

lookupIndexVar :: Index v -> Environment value v -> Var
lookupIndexVar index env =
  Index.Map.index (indices env) index

lookupIndexValue :: Index v -> Environment value v -> Maybe value
lookupIndexValue index env =
  lookupVarValue (lookupIndexVar index env) env

lookupVarValue :: Var -> Environment value v -> Maybe value
lookupVarValue v env =
  EnumMap.lookup v $ values env
