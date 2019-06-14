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
import Data.IntSequence (IntSeq)
import qualified Query
import qualified Data.IntSequence as IntSeq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import Error (Error)
import qualified Error
import qualified Evaluation
import Index
import qualified Meta
import Monad
import Name (Name(Name))
import qualified Name
import qualified "this" Data.IntMap as IntMap
import qualified Readback
import qualified Scope
import qualified Span
import qualified Syntax
import Var

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , span :: !Span.Relative
  , vars :: IntSeq Var
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

empty :: Scope.KeyedName -> M (Context Void)
empty key = do
  ms <- liftIO $ newIORef Meta.empty
  es <- liftIO $ newIORef mempty
  pure Context
    { scopeKey = key
    , span = Span.Relative 0 0
    , nameVars = mempty
    , varNames = mempty
    , vars = mempty
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
    , vars = mempty
    , values = mempty
    , types = mempty
    , boundVars = mempty
    , metas = metas context
    , errors = errors context
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

lookupNameIndex :: Name.Pre -> Context v -> Maybe (Index v)
lookupNameIndex (Name.Pre name) context = do
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
    i <- atomicModifyIORef (metas context) $ Meta.insert closedType (span context)
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
          headValue' <- Evaluation.evaluate Domain.empty headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved {} ->
          pure value

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
