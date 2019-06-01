{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Context where

import Protolude hiding (IntMap, force)

import Data.Coerce
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef

import "this" Data.IntMap (IntMap)
import qualified Builtin
import qualified Domain
import qualified Evaluation
import Index
import IntSequence (IntSeq)
import qualified IntSequence as IntSeq
import qualified Meta
import Monad
import Name (Name(Name))
import qualified Presyntax
import qualified "this" Data.IntMap as IntMap
import qualified Readback
import qualified Resolution
import qualified Syntax
import Var

data Context v = Context
  { resolutionKey :: !Resolution.KeyedName
  , vars :: IntSeq Var
  , nameVars :: HashMap Name Var
  , varNames :: IntMap Var Name
  , values :: IntMap Var (Lazy Domain.Value)
  , types :: IntMap Var (Lazy Domain.Type)
  , boundVars :: IntSeq Var
  , metas :: !(IORef (Meta.Vars (Syntax.Term Void)))
  }

toEvaluationEnvironment
  :: Context v
  -> Domain.Environment v
toEvaluationEnvironment context =
  Domain.Environment
    { vars = vars context
    , values = values context
    }

toReadbackEnvironment
  :: Context v
  -> Readback.Environment v
toReadbackEnvironment context =
  Readback.Environment
    { vars = vars context
    }

empty :: Resolution.KeyedName -> M (Context Void)
empty key = do
  ms <- liftIO $ newIORef Meta.empty
  pure Context
    { resolutionKey = key
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
    { resolutionKey = resolutionKey context
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
  -> Name
  -> Lazy Domain.Type
  -> M (Context (Succ v), Var)
extend context name type_ = do
  var <- freshVar
  pure
    ( context
      { nameVars = HashMap.insert name var $ nameVars context
      , varNames = IntMap.insert var name $ varNames context
      , vars = vars context IntSeq.:> var
      , types = IntMap.insert var type_ (types context)
      , boundVars = boundVars context IntSeq.:> var
      }
    , var
    )

extendDef
  :: Context v
  -> Name
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> M (Context (Succ v), Var)
extendDef context name value type_ = do
  var <- freshVar
  pure
    ( context
      { nameVars = HashMap.insert name var $ nameVars context
      , varNames = IntMap.insert var name $ varNames context
      , vars = vars context IntSeq.:> var
      , values = IntMap.insert var value (values context)
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )

lookupNameIndex :: Presyntax.Name -> Context v -> Maybe (Index v)
lookupNameIndex (Presyntax.Name name) context = do
  var <- HashMap.lookup (Name name) (nameVars context)
  pure $ lookupVarIndex var context

lookupVarIndex :: Var -> Context v -> Index v
lookupVarIndex var context =
  Index
    $ IntSeq.length (vars context)
    - fromMaybe (panic "Context.lookupVarIndex") (IntSeq.elemIndex var (vars context))
    - 1

lookupVarName :: Var -> Context v -> Name
lookupVarName var context =
  fromMaybe (panic "Context.lookupVarName")
    $ IntMap.lookup var
    $ varNames context

lookupIndexType :: Index v -> Context v -> Lazy Domain.Type
lookupIndexType (Index i) context =
  lookupVarType (IntSeq.index (vars context) (IntSeq.length (vars context) - i - 1)) context

lookupVarType :: Var -> Context v -> Lazy Domain.Type
lookupVarType var context =
  fromMaybe (panic "Context.lookupVarType")
    $ IntMap.lookup var
    $ types context

lookupVarValue :: Var -> Context v -> Maybe (Lazy Domain.Type)
lookupVarValue var context =
  IntMap.lookup var (values context)

newMeta :: Domain.Type -> Context v -> M Domain.Value
newMeta type_ context = do
  closedType <- piBoundVars context type_
  liftIO $ do
    i <- atomicModifyIORef (metas context) $ Meta.insert closedType
    pure $ Domain.Neutral (Domain.Meta i) (Lazy . pure . Domain.var <$> IntSeq.toTsil (boundVars context))

newMetaType :: Context v -> M Domain.Value
newMetaType =
  newMeta Builtin.type_

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void)
piBoundVars context type_ = do
  type' <-
    Readback.readback
      Readback.Environment
        { vars = boundVars context
        }
      type_

  pis (boundVars context) type'
  where
    pis :: IntSeq Var -> Syntax.Type v -> M (Syntax.Type v')
    pis vars_ term =
      case vars_ of
        IntSeq.Empty ->
          pure $ coerce term

        vars' IntSeq.:> var -> do
          varType <- force $ lookupVarType var context
          varType' <-
            Readback.readback
              Readback.Environment
                { vars = vars'
                }
              varType
          let
            term' = Syntax.Pi (lookupVarName var context) varType' $ coerce term
          pis vars' term'

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var (Syntax.Term void))
lookupMeta i context =
  liftIO $ do
    m <- readIORef (metas context)
    pure $ coerce $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term =
  liftIO $
    atomicModifyIORef (metas context) $ \m ->
      (Meta.solve i term m, ())

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
        Meta.Solved headValue _ -> do
          headValue' <- Evaluation.evaluate Domain.empty headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved _ ->
          pure value

    _ ->
      pure value
