{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Context where

import Protolude hiding (IntMap, force)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef

import "this" Data.IntMap (IntMap)
import qualified Builtin
import Data.IntSequence (IntSeq)
import qualified Data.IntSequence as IntSeq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import Error (Error)
import qualified Error
import qualified Evaluation
import Index
import qualified Index.Map
import qualified Index.Map as Index
import qualified Meta
import Monad
import Name (Name(Name))
import qualified Name
import Plicity
import qualified "this" Data.IntMap as IntMap
import qualified Query
import qualified Readback
import qualified Scope
import qualified Span
import qualified Syntax
import Var

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , span :: !Span.Relative
  , indices :: Index.Map v Var
  , nameVars :: HashMap Name Var
  , varNames :: IntMap Var Name
  , values :: IntMap Var (Lazy Domain.Value)
  , types :: IntMap Var (Lazy Domain.Type)
  , boundVars :: IntSeq Var
  , metas :: !(IORef (Meta.Vars (Syntax.Term Void)))
  , errors :: !(IORef (Tsil Error))
  }

toEvaluationEnvironment
  :: Context v
  -> Domain.Environment v
toEvaluationEnvironment context =
  Domain.Environment
    { scopeKey = scopeKey context
    , indices = indices context
    , values = values context
    }

toReadbackEnvironment
  :: Context v
  -> Readback.Environment v
toReadbackEnvironment context =
  Readback.Environment
    { indices = indices context
    , values = values context
    }

empty :: Scope.KeyedName -> M (Context Void)
empty key = do
  ms <- liftIO $ newIORef Meta.empty
  es <- liftIO $ newIORef mempty
  pure Context
    { scopeKey = key
    , span = Span.Relative 0 0
    , nameVars = mempty
    , varNames = mempty
    , indices = Index.Map.Empty
    , values = mempty
    , types = mempty
    , boundVars = mempty
    , metas = ms
    , errors = es
    }

emptyFrom :: Context v -> Context Void
emptyFrom context =
  Context
    { scopeKey = scopeKey context
    , span = span context
    , nameVars = mempty
    , varNames = mempty
    , indices = Index.Map.Empty
    , values = mempty
    , types = mempty
    , boundVars = mempty
    , metas = metas context
    , errors = errors context
    }

-- TODO should this take a Name.Pre instead?
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
      , indices = indices context Index.Map.:> var
      , types = IntMap.insert var type_ (types context)
      , boundVars = boundVars context IntSeq.:> var
      }
    , var
    )

extendUnnamed
  :: Context v
  -> Name
  -> Lazy Domain.Type
  -> M (Context (Succ v), Var)
extendUnnamed context name type_ = do
  var <- freshVar
  pure
    ( context
      { varNames = IntMap.insert var name $ varNames context
      , indices = indices context Index.Map.:> var
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
      , indices = indices context Index.Map.:> var
      , values = IntMap.insert var value (values context)
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )

extendUnnamedDef
  :: Context v
  -> Name
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> M (Context (Succ v), Var)
extendUnnamedDef context name value type_ = do
  var <- freshVar
  pure
    ( context
      { varNames = IntMap.insert var name $ varNames context
      , indices = indices context Index.Map.:> var
      , values = IntMap.insert var value (values context)
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )

extendUnindexedDef
  :: Context v
  -> Name
  -> Lazy Domain.Value
  -> Lazy Domain.Type
  -> M (Context v, Var)
extendUnindexedDef context name value type_ = do
  var <- freshVar
  pure
    ( context
      { nameVars = HashMap.insert name var $ nameVars context
      , varNames = IntMap.insert var name $ varNames context
      , values = IntMap.insert var value (values context)
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )

extendUnindexedDefs
  :: Context v
  -> Tsil (Name, Lazy Domain.Value, Lazy Domain.Type)
  -> M (Context v)
extendUnindexedDefs context defs =
  case defs of
    Tsil.Empty ->
      pure context

    defs' Tsil.:> (name, value, type_) -> do
      context' <- extendUnindexedDefs context defs'
      (context'', _) <- extendUnindexedDef context' name value type_
      pure context''

extendBefore :: Context v -> Var -> Name -> Lazy Domain.Type -> M (Context (Succ v), Var)
extendBefore context beforeVar name type_ = do
  var <- freshVar
  pure
    ( context
      { varNames = IntMap.insert var name $ varNames context
      , indices = indices context Index.Map.:> var
      , types = IntMap.insert var type_ (types context)
      , boundVars =
        case IntSeq.elemIndex beforeVar $ boundVars context of
          Nothing ->
            panic "extendBefore no such var"

          Just i ->
            IntSeq.insertAt i var $ boundVars context
      }
    , var
    )

define :: Context v -> Var -> Lazy Domain.Value -> Context v
define context var value =
  context
    { values = IntMap.insert var value $ values context
    , boundVars = IntSeq.delete var $ boundVars context
    }

lookupNameVar :: Name.Pre -> Context v -> Maybe Var
lookupNameVar (Name.Pre name) context =
  HashMap.lookup (Name name) (nameVars context)

lookupVarIndex :: Var -> Context v -> Maybe (Index v)
lookupVarIndex var context =
  Index.Map.elemIndex var (indices context)

lookupVarName :: Var -> Context v -> Name
lookupVarName var context =
  fromMaybe (panic "Context.lookupVarName")
    $ IntMap.lookup var
    $ varNames context

lookupIndexVar :: Index v -> Context v -> Var
lookupIndexVar index context =
  Index.Map.index (indices context) index

lookupIndexType :: Index v -> Context v -> Lazy Domain.Type
lookupIndexType index context =
  lookupVarType (lookupIndexVar index context) context

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
    i <- atomicModifyIORef (metas context) $ Meta.insert closedType (span context)
    pure $ Domain.Neutral (Domain.Meta i) ((Explicit,) . Lazy . pure . Domain.var <$> IntSeq.toTsil (boundVars context))

newMetaType :: Context v -> M Domain.Value
newMetaType =
  newMeta Builtin.type_

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void)
piBoundVars context type_ = do
  type' <-
    Readback.readback
      Readback.Environment
        { indices = Index.Map $ boundVars context
        , values = values context
        }
      type_

  pis (boundVars context) type'
  where
    pis :: IntSeq Var -> Syntax.Type v -> M (Syntax.Type v')
    pis vars_ term =
      case vars_ of
        IntSeq.Empty ->
          pure $ Syntax.coerce term

        vars' IntSeq.:> var -> do
          varType <- force $ lookupVarType var context
          varType' <-
            Readback.readback
              Readback.Environment
                { indices = Index.Map vars'
                , values = values context
                }
              varType
          let
            term' = Syntax.Pi (lookupVarName var context) varType' Explicit $ Syntax.succ term
          pis vars' term'

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var (Syntax.Term void))
lookupMeta i context =
  liftIO $ do
    m <- readIORef (metas context)
    pure $ Syntax.coerce <$> Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term =
  liftIO $
    atomicModifyIORef (metas context) $ \m ->
      (Meta.solve i term m, ())

spanned :: Span.Relative -> Context v -> Context v
spanned s context =
  context
    { span = s
    }

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
          headValue' <- Evaluation.evaluate (Domain.empty $ scopeKey context) headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved {} ->
          pure value

    Domain.Case scrutinee branches@(Domain.Branches branchEnv brs)  -> do
      scrutinee' <- forceHead context scrutinee
      case scrutinee' of
        Domain.Neutral (Domain.Con constr) spine -> do
          value' <- Evaluation.chooseBranch branchEnv constr (toList spine) brs
          forceHead context value'

        _ ->
          pure $ Domain.Case scrutinee' branches

    _ ->
      pure value

-------------------------------------------------------------------------------
-- Error reporting

report :: Context v -> Error.Elaboration -> M ()
report context err =
  let
    err' =
      Error.Elaboration (scopeKey context) $
      Error.Spanned (span context) err
  in
  liftIO $ atomicModifyIORef (errors context) $ \errs ->
    (errs Tsil.:> err', ())

reportParseError :: Context v -> Error.Parsing -> M ()
reportParseError context err =
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      Context.scopeKey context

    filePath =
      Query.moduleFilePath module_

    err' =
      Error.Parse filePath err
  in
  liftIO $ atomicModifyIORef (errors context) $ \errs ->
    (errs Tsil.:> err', ())

try :: Context v -> M a -> M (Maybe a)
try context m =
  (Just <$> m) `catchError` \err -> do
    report context err
    pure Nothing

try_ :: Context v -> M () -> M Bool
try_ context m =
  (True <$ m) `catchError` \err -> do
    report context err
    pure False
