{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
module Context where

import Protolude hiding (Seq, force)

import Data.Coerce
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef

import qualified Builtin
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
  , metas :: !(IORef (Meta.Vars (Syntax.Type Void) (Syntax.Term Void)))
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

emptyFrom :: Context v -> Context Void
emptyFrom context =
  Context
    { nextVar = nextVar context
    , nameVars = mempty
    , varNames = mempty
    , vars = mempty
    , values = mempty
    , types = mempty
    , boundVars = mempty
    , metas = metas context
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
  -> IO (Context (Succ v), Var)
extendDef context name value type_ = do
  var@(Var v) <- readIORef (nextVar context)
  writeIORef (nextVar context) (Var (v + 1))
  pure
    ( context
      { nameVars = HashMap.insert name var $ nameVars context
      , varNames = HashMap.insert var name $ varNames context
      , vars = vars context Seq.:> var
      , values = HashMap.insert var value (values context)
      , types = HashMap.insert var type_ (types context)
      }
    , var
    )

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
  fromMaybe (panic "Context.lookupVarName")
    $ HashMap.lookup var
    $ varNames context

lookupIndexType :: Index v -> Context v -> Lazy Domain.Type
lookupIndexType (Index i) context =
  lookupVarType (Seq.index (vars context) (Seq.length (vars context) - i - 1)) context

lookupVarType :: Var -> Context v -> Lazy Domain.Type
lookupVarType var context =
  fromMaybe (panic "Context.lookupVarType")
    $ HashMap.lookup var
    $ types context

lookupVarValue :: Var -> Context v -> Maybe (Lazy Domain.Type)
lookupVarValue var context =
  HashMap.lookup var (values context)

newMeta :: Domain.Type -> Context v -> M Domain.Value
newMeta type_ context = do
  closedType <- piBoundVars context type_
  m <- readIORef (metas context)
  let
    (m', i) = Meta.insert closedType m
  writeIORef (metas context) m'

  pure $ Domain.Neutral (Domain.Meta i) (Lazy . pure . Domain.var <$> Seq.toTsil (boundVars context))

newMetaType :: Context v -> M Domain.Value
newMetaType =
  newMeta Builtin.type_

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void)
piBoundVars context type_ = do
  type' <-
    Readback.readback
      Readback.Environment
        { nextVar = nextVar context
        , vars = boundVars context
        }
      type_

  pis (boundVars context) type'
  where
    pis :: Seq Var -> Syntax.Type v -> M (Syntax.Type v')
    pis vars_ term =
      case vars_ of
        Seq.Empty ->
          pure $ coerce term

        vars' Seq.:> var -> do
          varType <- force $ lookupVarType var context
          varType' <-
            Readback.readback
              Readback.Environment
                { nextVar = nextVar context
                , vars = vars'
                }
              varType
          let
            term' = Syntax.Pi (lookupVarName var context) varType' $ coerce term
          pis vars' term'

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var (Syntax.Type void) (Syntax.Term void))
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ coerce $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term = do
  m <- readIORef (metas context)
  let
    m' = Meta.solve i term m
  writeIORef (metas context) m'

-------------------------------------------------------------------------------

-- | Evaluate the head of a value further, if (now) possible due to meta
-- solutions or new value bindings.
forceHead
  :: Context v
  -> Domain.Value
  -> M Domain.Value
forceHead context value =
  case value of
    Domain.Neutral (Domain.Var var) spine
      | Just headValue <- Context.lookupVarValue var context -> do
        headValue' <- force headValue
        value' <- Evaluation.applySpine headValue' spine
        forceHead context value'

    Domain.Neutral (Domain.Meta metaIndex) spine -> do
      meta <- Context.lookupMeta metaIndex context

      case meta of
        Meta.Solved headValue -> do
          headValue' <- Evaluation.evaluate (Evaluation.empty (Context.nextVar context)) headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved _ ->
          pure value

    _ ->
      pure value
