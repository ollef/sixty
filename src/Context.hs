module Context where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import qualified Domain
import qualified Environment
import Environment (Environment)
import Index
import Monad

data Context v = Context
  { size :: !(Environment.Size v)
  , names :: HashMap Text Level
  , values :: Environment v (Lazy Domain.Value)
  , types :: Environment v (Lazy Domain.Type)
  }

extend
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> (Context (Succ v), Level)
extend (Context sz ns vs ts) name type_ =
  let
    (sz', level) =
      Environment.extendSize sz
  in
  ( Context
    sz'
    (HashMap.insert name level ns)
    (Environment.Snoc vs $ Lazy $ pure $ Domain.var level)
    (Environment.Snoc ts type_)
  , level
  )

extendValue
  :: Context v
  -> Text
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> Context (Succ v)
extendValue (Context sz ns vs ts) name value type_ =
  let
    (sz', level) =
      Environment.extendSize sz
  in
  Context
    sz'
    (HashMap.insert name level ns)
    (Environment.Snoc vs value)
    (Environment.Snoc ts type_)

lookupName :: Text -> Context v -> Maybe (Index v)
lookupName name context = do
  level <- HashMap.lookup name (names context)
  return $ Index.fromLevel level (size context)

lookupValue :: Index v -> Context v -> Lazy Domain.Value
lookupValue v context = Environment.lookup (values context) v

lookupType :: Index v -> Context v -> Lazy Domain.Type
lookupType v context = Environment.lookup (types context) v
