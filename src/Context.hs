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
  , nameVars :: HashMap Text Var
  , varNames :: HashMap Var Text
  , values :: HashMap Var (Lazy Domain.Value)
  , types :: HashMap Var (Lazy Domain.Type)
  , boundVars :: Seq Var
  , metas :: !(IORef (Meta.Vars (Lazy Domain.Value, Syntax.Term Void)))
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
    , nameVars = mempty
    , varNames = mempty
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
      { nameVars = HashMap.insert name var $ nameVars context
      , varNames = HashMap.insert var name $ varNames context
      , vars = vars context Seq.:> var
      , types = HashMap.insert var type_ (types context)
      , boundVars = boundVars context Seq.:> var
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
    { nameVars = HashMap.insert name var $ nameVars context
    , varNames = HashMap.insert var name $ varNames context
    , vars = vars context Seq.:> var
    , values = HashMap.insert var value (values context)
    , types = HashMap.insert var type_ (types context)
    }

lookupNameIndex :: Text -> Context v -> Maybe (Index v)
lookupNameIndex name context = do
  var <- HashMap.lookup name (nameVars context)
  pure $ lookupVarIndex var context

lookupVarIndex :: Var -> Context v -> Index v
lookupVarIndex var context =
  Index
    $ Seq.length (vars context)
    - fromMaybe (panic "Context.lookupVarIndex") (Seq.elemIndex var (vars context))
    - 1

lookupVarName :: Var -> Context v -> Text
lookupVarName var context =
  varNames context HashMap.! var

lookupIndexType :: Index v -> Context v -> Lazy Domain.Type
lookupIndexType (Index i) context =
  lookupVarType (Seq.index (vars context) (Seq.length (vars context) - i - 1)) context

lookupVarType :: Var -> Context v -> Lazy Domain.Type
lookupVarType v context =
  types context HashMap.! v

lookupVarValue :: Var -> Context v -> Maybe (Lazy Domain.Type)
lookupVarValue var context =
  HashMap.lookup var (values context)

newMeta :: Context v -> M Domain.Value
newMeta context = do
  m <- readIORef (metas context)
  let
    (m', i) = Meta.insert m
  writeIORef (metas context) m'

  pure $ Domain.Neutral (Domain.Meta i) (Lazy . pure . Domain.var <$> Seq.toTsil (boundVars context))

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var (Lazy Domain.Value, Syntax.Term Void))
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term = do
  m <- readIORef (metas context)
  value <- lazy $
    Evaluation.evaluate (Evaluation.empty (nextVar context)) term
  let
    m' = Meta.solve i (value, term) m
  writeIORef (metas context) m'
