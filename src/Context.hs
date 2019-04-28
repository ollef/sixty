module Context where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef

import qualified Domain
import qualified Environment
import Environment (Environment)
import Index
import qualified Meta
import Monad
import qualified Syntax
import Tsil (Tsil)
import qualified Tsil

data Context v = Context
  { size :: !(Environment.Size v)
  , names :: HashMap Text Level
  , values :: Environment v (Lazy Domain.Value)
  , types :: Environment v (Lazy Domain.Type)
  , boundLevels :: Tsil Level
  , metas :: !(IORef (Meta.Map Domain.Value))
  }

empty :: M (Context Void)
empty = do
  ms <- newIORef Meta.empty
  pure Context
    { size = Zero
    , names = mempty
    , values = Environment.Nil
    , types = Environment.Nil
    , boundLevels = mempty
    , metas = ms
    }

extend
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> (Context (Succ v), Level)
extend context name type_ =
  let
    (size', level) =
      Environment.extendSize $ size context
  in
  ( context
    { size = size'
    , names = HashMap.insert name level $ names context
    , values = Environment.Snoc (values context) $ Lazy $ pure $ Domain.var level
    , types = Environment.Snoc (types context) type_
    , boundLevels = Tsil.Snoc (boundLevels context) level
    }
  , level
  )

extendDef
  :: Context v
  -> Text
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> Context (Succ v)
extendDef context name value type_ =
  let
    (size', level) =
      Environment.extendSize $ size context
  in
  context
    { size = size'
    , names = HashMap.insert name level $ names context
    , values = Environment.Snoc (values context) value
    , types = Environment.Snoc (types context) type_
    }

lookupName :: Text -> Context v -> Maybe (Index v)
lookupName name context = do
  level <- HashMap.lookup name (names context)
  return $ Index.fromLevel level (size context)

lookupValue :: Index v -> Context v -> Lazy Domain.Value
lookupValue v context = Environment.lookup (values context) v

lookupType :: Index v -> Context v -> Lazy Domain.Type
lookupType v context = Environment.lookup (types context) v

newMeta :: Context v -> M (Syntax.Term v)
newMeta context = do
  m <- readIORef (metas context)
  let
    (m', i) = Meta.insert m
  writeIORef (metas context) m'

  let
    toVar level =
      Syntax.Var (Index.fromLevel level (size context))
    args =
      toVar <$> boundLevels context

  pure $ Syntax.apps (Syntax.Meta i) args

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var Domain.Value)
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ Meta.lookup i m
