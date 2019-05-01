{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
module Context where

import Protolude hiding (Seq)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef

import qualified Domain
import qualified Evaluation
import Index
import qualified Meta
import Monad
import qualified Readback
import Sequence (Seq)
import qualified Sequence as Seq
import qualified Syntax
import Var

data Context v = Context
  { nextVar :: !(IORef Var)
  , vars :: Seq Var
  , names :: HashMap Text Var
  , values :: HashMap Var (Lazy Domain.Value)
  , types :: HashMap Var (Lazy Domain.Type)
  , boundVars :: Seq Var
  , metas :: !(IORef (Meta.Vars Domain.Value))
  }

toEvaluationEnvironment
  :: Context v
  -> Evaluation.Environment v
toEvaluationEnvironment context =
  Evaluation.Environment
    { nextVar = nextVar context
    , vars = vars context
    , values = values context
    }

toReadbackEnvironment
  :: Context v
  -> Readback.Environment v
toReadbackEnvironment context =
  Readback.Environment
    { nextVar = nextVar context
    , vars = vars context
    }

empty :: M (Context Void)
empty = do
  nv <- newIORef (Var 0)
  ms <- newIORef Meta.empty
  pure Context
    { nextVar = nv
    , names = mempty
    , vars = mempty
    , values = mempty
    , types = mempty
    , boundVars = mempty
    , metas = ms
    }

extend
  :: Context v
  -> Text
  -> Lazy Domain.Type
  -> M (Context (Succ v), Var)
extend context name type_ = do
  var@(Var v) <- readIORef (nextVar context)
  writeIORef (nextVar context) (Var (v + 1))
  pure
    ( context
      { names = HashMap.insert name var $ names context
      , vars = vars context Seq.|> var
      , values = HashMap.insert var (Lazy $ pure $ Domain.var var) (values context)
      , types = HashMap.insert var type_ (types context)
      , boundVars = boundVars context Seq.|> var
      }
    , var
    )

extendDef
  :: Context v
  -> Text
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> IO (Context (Succ v))
extendDef context name value type_ = do
  var@(Var v) <- readIORef (nextVar context)
  writeIORef (nextVar context) (Var (v + 1))
  pure context
    { names = HashMap.insert name var $ names context
    , vars = vars context Seq.|> var
    , values = HashMap.insert var value (values context)
    , types = HashMap.insert var type_ (types context)
    }

lookupName :: Text -> Context v -> Maybe (Index v)
lookupName name context = do
  var <- HashMap.lookup name (names context)
  pure $ lookupIndex var context

lookupIndex :: Var -> Context v -> Index v
lookupIndex var context =
  Index
    $ Seq.length (vars context)
    - fromMaybe (panic "Context.lookupIndex") (Seq.elemIndex var (vars context))
    - 1

lookupType :: Index v -> Context v -> Lazy Domain.Type
lookupType (Index i) context =
  types context HashMap.! Seq.index (vars context) (Seq.length (vars context) - i - 1)

lookupValue :: Var -> Context v -> Maybe (Lazy Domain.Type)
lookupValue var context =
  HashMap.lookup var (values context)

newMeta :: Context v -> M (Syntax.Term v)
newMeta context = do
  m <- readIORef (metas context)
  let
    (m', i) = Meta.insert m
  writeIORef (metas context) m'

  let
    toSyntax var = Syntax.Var (lookupIndex var context)
    args = toSyntax <$> toList (boundVars context)

  pure $ Syntax.apps (Syntax.Meta i) args

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var Domain.Value)
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ Meta.lookup i m
