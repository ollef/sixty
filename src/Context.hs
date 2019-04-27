module Context where

import Protolude

import qualified Bound.Var as Bound
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import qualified Domain
import Index
import Monad
import qualified Syntax

data Context v = Context
  { size :: !(Domain.EnvSize v)
  , names :: HashMap Text Level
  , values :: Syntax.Env (Lazy Domain.Value) v
  , types :: Syntax.Env (Lazy Domain.Type) v
  }

extend
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> (Context (Bound.Var () v), Level)
extend (Context sz ns vs ts) name type_ =
  let
    (sz', level) =
      Domain.extendEnvSize sz
  in
  ( Context
    sz'
    (HashMap.insert name level ns)
    (Syntax.Snoc vs $ Lazy $ pure $ Domain.var level)
    (Syntax.Snoc ts type_)
  , level
  )

extendValue
  :: Context v
  -> Text
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> Context (Bound.Var () v)
extendValue (Context sz ns vs ts) name value type_ =
  let
    (sz', level) =
      Domain.extendEnvSize sz
  in
  Context
    sz'
    (HashMap.insert name level ns)
    (Syntax.Snoc vs value)
    (Syntax.Snoc ts type_)

lookupName :: Text -> Context v -> Maybe (Index v)
lookupName name context = do
  level <- HashMap.lookup name (names context)
  return $ Index.fromLevel level (size context)

lookupValue :: Index v -> Context v -> Lazy Domain.Value
lookupValue v context = Syntax.lookupValue (values context) v

lookupType :: Index v -> Context v -> Lazy Domain.Type
lookupType v context = Syntax.lookupValue (types context) v
