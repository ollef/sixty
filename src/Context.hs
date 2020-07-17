{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Context where

import Protolude hiding (IntMap, IntSet, catch, force)

import Control.Exception.Lifted
import Control.Monad.Base
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef.Lifted
import Rock

import qualified Binding
import qualified Bindings
import Bindings (Bindings)
import qualified Builtin
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Core.Domain as Domain
import Core.Domain.Pattern (Pattern)
import Environment (Environment(Environment))
import qualified Environment
import Error (Error)
import qualified Error
import qualified Error.Parsing as Error
import qualified Core.Evaluation as Evaluation
import Index
import qualified Index.Map
import qualified Index.Map as Index
import qualified Meta
import Monad
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Surface.Syntax as Surface
import qualified Query
import qualified Core.Readback as Readback
import qualified Scope
import qualified Span
import qualified Core.Syntax as Syntax
import Telescope (Telescope)
import qualified Telescope
import Var
import qualified Core.Zonking as Zonking

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , span :: !Span.Relative
  , indices :: Index.Map v Var
  , nameVars :: HashMap Name Var
  , varNames :: IntMap Var Name
  , values :: IntMap Var Domain.Value
  , types :: IntMap Var Domain.Type
  , boundVars :: IntSeq Var
  , metas :: !(IORef (Meta.Vars (Syntax.Term Void)))
  , errors :: !(IORef (Tsil Error))
  }

toEnvironment
  :: Context v
  -> Domain.Environment v
toEnvironment context =
  Environment
    { scopeKey = scopeKey context
    , indices = indices context
    , values = values context
    }

toPrettyableTerm :: Context v -> Syntax.Term v -> M Error.PrettyableTerm
toPrettyableTerm context term = do
  term' <- zonk context term
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      Context.scopeKey context
  pure $
    Error.PrettyableTerm
      module_
      ((`lookupVarName` context) <$> toList (indices context))
      (Syntax.coerce term')

toPrettyableClosedTerm :: Context v -> Syntax.Term Void -> M Error.PrettyableTerm
toPrettyableClosedTerm context term = do
  term' <- zonk (emptyFrom context) term
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      Context.scopeKey context
  pure $ Error.PrettyableTerm module_ mempty (Syntax.coerce term')

toPrettyablePattern :: Context v -> Pattern -> Error.PrettyablePattern
toPrettyablePattern context = do
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      Context.scopeKey context
  Error.PrettyablePattern
    module_
    ((`lookupVarName` context) <$> toList (indices context))

empty :: MonadBase IO m => Scope.KeyedName -> m (Context Void)
empty key = do
  ms <- newIORef Meta.empty
  es <- newIORef mempty
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

extendPre
  :: Context v
  -> Surface.SpannedName
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendPre context (Surface.SpannedName _ name) type_ = do
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

extend
  :: Context v
  -> Name
  -> Domain.Type
  -> M (Context (Succ v), Var)
extend context name type_ = do
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

extendPreDef
  :: Context v
  -> Name
  -> Domain.Value
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendPreDef context name value type_ = do
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

extendDef
  :: Context v
  -> Name
  -> Domain.Value
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendDef context name value type_ = do
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
  -> Bindings
  -> Domain.Value
  -> Domain.Type
  -> M (Context v, Var)
extendUnindexedDef context bindings value type_ = do
  var <- freshVar
  let
    name =
      Bindings.toName bindings
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
  -> Tsil (Bindings, Domain.Value, Domain.Type)
  -> M (Context v)
extendUnindexedDefs context defs =
  case defs of
    Tsil.Empty ->
      pure context

    defs' Tsil.:> (bindings, value, type_) -> do
      context' <- extendUnindexedDefs context defs'
      (context'', _) <- extendUnindexedDef context' bindings value type_
      pure context''

extendBefore
  :: Context v
  -> Var
  -> Bindings
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendBefore context beforeVar binding type_ = do
  var <- freshVar
  pure
    ( context
      { varNames = IntMap.insert var (Bindings.toName binding) $ varNames context
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

defineWellOrdered :: Context v -> Var -> Domain.Value -> Context v
defineWellOrdered context var value =
  context
    { values = IntMap.insert var value $ values context
    , boundVars = IntSeq.delete var $ boundVars context
    }

define :: Context v -> Var -> Domain.Value -> M (Context v)
define context var value = do
  deps <- evalStateT (dependencies context value) mempty
  let
    context' =
      defineWellOrdered context var value

    (pre, post) =
      Tsil.partition (`IntSet.member` deps) $
      IntSeq.toTsil $
      boundVars context'

  pure context'
    { boundVars =
      IntSeq.fromTsil pre <> IntSeq.fromTsil post
    }

-- TODO: Move
dependencies
  :: Context v
  -> Domain.Value
  -> StateT (IntMap Var (IntSet Var)) M (IntSet Var)
dependencies context value = do
  value' <- lift $ Context.forceHeadGlue context value
  case value' of
    Domain.Neutral hd spine -> do
      spineVars <- mapM (dependencies context . snd) spine
      hdVars <- headVars hd
      pure $ hdVars <> fold spineVars

    Domain.Con _ args ->
      fold <$> mapM (dependencies context . snd) args

    Domain.Lit _ ->
      pure mempty

    Domain.Glued (Domain.Global _) spine _ -> do
      spineVars <- mapM (dependencies context . snd) spine
      pure $ fold spineVars

    Domain.Glued _ _ value'' -> do
      value''' <- lift $ force value''
      dependencies context value'''

    Domain.Lam bindings type' _ closure ->
      abstractionDependencies (Bindings.toName bindings) type' closure

    Domain.Pi binding type' _ closure ->
      abstractionDependencies (Binding.toName binding) type' closure

    Domain.Fun domain _ target -> do
      domainVars <- dependencies context domain
      targetVars <- dependencies context target
      pure $ domainVars <> targetVars

  where
    abstractionDependencies name type' closure = do
      typeVars <- dependencies context type'
      (context', var) <- lift $ extend context name type'
      body <- lift $ Evaluation.evaluateClosure closure $ Domain.var var
      bodyVars <- dependencies context' body
      pure $ typeVars <> IntSet.delete var bodyVars

    headVars hd =
      case hd of
        Domain.Var v
          | v `IntSeq.member` boundVars context -> do
            cache <- get
            typeDeps <- case IntMap.lookup v cache of
              Nothing -> do
                typeDeps <- dependencies context $ lookupVarType v context
                modify $ IntMap.insert v typeDeps
                pure typeDeps

              Just typeDeps ->
                pure typeDeps

            pure $ typeDeps <> IntSet.singleton v

          | otherwise ->
            pure $ IntSet.singleton v

        Domain.Global _ ->
          pure mempty

        Domain.Meta _ ->
          pure mempty

        Domain.Case scrutinee (Domain.Branches env branches defaultBranch) -> do
          scrutineeVars <- dependencies context scrutinee
          defaultBranchVars <- mapM (dependencies context <=< lift . Evaluation.evaluate env) defaultBranch
          brVars <- branchVars context env branches
          pure $ scrutineeVars <> fold defaultBranchVars <> brVars

    branchVars
      :: Context v
      -> Domain.Environment v'
      -> Syntax.Branches v'
      -> StateT (IntMap Var (IntSet Var)) M (IntSet Var)
    branchVars context' env branches =
      fold <$>
        case branches of
          Syntax.ConstructorBranches _ constructorBranches ->
            mapM (telescopeVars context' env . snd) $ toList constructorBranches

          Syntax.LiteralBranches literalBranches ->
            forM (toList literalBranches) $ \(_, branch) -> do
              branch' <- lift $ Evaluation.evaluate env branch
              dependencies context' branch'

    telescopeVars
      :: Context v
      -> Domain.Environment v'
      -> Telescope Bindings Syntax.Type Syntax.Term v'
      -> StateT (IntMap Var (IntSet Var)) M (IntSet Var)
    telescopeVars context' env tele =
      case tele of
        Telescope.Empty body -> do
          body' <- lift $ Evaluation.evaluate env body
          dependencies context' body'

        Telescope.Extend binding domain _ tele' -> do
          domain' <- lift $ Evaluation.evaluate env domain
          domainVars <- dependencies context' domain'
          (context'', var) <- lift $ extend context' (Bindings.toName binding) domain'
          let
            env' =
              Environment.extendVar env var

          rest <- telescopeVars context'' env' tele'
          pure $ domainVars <> IntSet.delete var rest

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

lookupIndexType :: Index v -> Context v -> Domain.Type
lookupIndexType index context =
  lookupVarType (lookupIndexVar index context) context

lookupVarType :: Var -> Context v -> Domain.Type
lookupVarType var context =
  fromMaybe (panic "Context.lookupVarType")
    $ IntMap.lookup var
    $ types context

lookupVarValue :: Var -> Context v -> Maybe Domain.Type
lookupVarValue var context =
  IntMap.lookup var (values context)

newMeta :: Domain.Type -> Context v -> M Domain.Value
newMeta type_ context = do
  closedType <- piBoundVars context type_
  i <- atomicModifyIORef (metas context) $ Meta.insert closedType (span context)
  pure $ Domain.Neutral (Domain.Meta i) ((Explicit,) . Domain.var <$> IntSeq.toTsil (boundVars context))

newMetaType :: Context v -> M Domain.Value
newMetaType =
  newMeta Builtin.Type

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void)
piBoundVars context type_ = do
  type' <-
    Readback.readback
      Environment
        { scopeKey = scopeKey context
        , indices = Index.Map $ boundVars context
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
          let
            varType =
              lookupVarType var context
          varType' <-
            Readback.readback
              Environment
                { scopeKey = scopeKey context
                , indices = Index.Map vars'
                , values = values context
                }
              varType
          let
            term' = Syntax.Pi (Binding.Unspanned $ lookupVarName var context) varType' Explicit $ Syntax.succ term
          pis vars' term'

lookupMeta
  :: Meta.Index
  -> Context v
  -> M (Meta.Var (Syntax.Term void))
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ Syntax.coerce <$> Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term =
  atomicModifyIORef (metas context) $ \m ->
    (Meta.solve i term m, ())

spanned :: Span.Relative -> Context v -> Context v
spanned s context =
  context
    { span = s
    }

-------------------------------------------------------------------------------

-- | Evaluate the head of a value further, if (now) possible due to meta
-- solutions or new value bindings. Also evalutes through glued values.
forceHead
  :: Context v
  -> Domain.Value
  -> M Domain.Value
forceHead context value =
  case value of
    Domain.Neutral (Domain.Var var) spine
      | Just headValue <- Context.lookupVarValue var context -> do
        value' <- Evaluation.applySpine headValue spine
        forceHead context value'

    Domain.Neutral (Domain.Meta metaIndex) spine -> do
      meta <- Context.lookupMeta metaIndex context

      case meta of
        Meta.Solved headValue _ -> do
          headValue' <- Evaluation.evaluate (Environment.empty $ scopeKey context) headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved {} ->
          pure value

    Domain.Neutral (Domain.Case scrutinee branches@(Domain.Branches branchEnv brs defaultBranch)) spine -> do
      scrutinee' <- forceHead context scrutinee
      case (scrutinee', brs) of
        (Domain.Con constr constructorArgs, Syntax.ConstructorBranches _ constructorBranches) -> do
          value' <- Evaluation.chooseConstructorBranch branchEnv constr (toList constructorArgs) constructorBranches defaultBranch
          value'' <- forceHead context value'
          Evaluation.applySpine value'' spine

        (Domain.Lit lit, Syntax.LiteralBranches literalBranches) -> do
          value' <- Evaluation.chooseLiteralBranch branchEnv lit literalBranches defaultBranch
          value'' <- forceHead context value'
          Evaluation.applySpine value'' spine

        _ ->
          pure $ Domain.Neutral (Domain.Case scrutinee' branches) spine

    Domain.Glued _ _ value' -> do
      value'' <- force value'
      forceHead context value''

    _ ->
      pure value

-- | Evaluate the head of a value further, if (now) possible due to meta
-- solutions or new value bindings, returning glued values.
forceHeadGlue
  :: Context v
  -> Domain.Value
  -> M Domain.Value
forceHeadGlue context value =
  case value of
    Domain.Neutral (Domain.Var var) spine
      | Just headValue <- Context.lookupVarValue var context -> do
        value' <- lazy $ do
          value' <- Evaluation.applySpine headValue spine
          forceHeadGlue context value'
        pure $ Domain.Glued (Domain.Var var) spine value'

    Domain.Neutral (Domain.Meta metaIndex) spine -> do
      meta <- Context.lookupMeta metaIndex context

      case meta of
        Meta.Solved headValue _ -> do
          value' <- lazy $ do
            headValue' <- Evaluation.evaluate (Environment.empty $ scopeKey context) headValue
            value' <- Evaluation.applySpine headValue' spine
            forceHeadGlue context value'
          pure $ Domain.Glued (Domain.Meta metaIndex) spine value'

        Meta.Unsolved {} ->
          pure value

    Domain.Neutral (Domain.Case scrutinee branches@(Domain.Branches branchEnv brs defaultBranch)) spine -> do
      scrutinee' <- forceHead context scrutinee
      case (scrutinee', brs) of
        (Domain.Con constr constructorArgs, Syntax.ConstructorBranches _ constructorBranches) -> do
          value' <- Evaluation.chooseConstructorBranch branchEnv constr (toList constructorArgs) constructorBranches defaultBranch
          value'' <- forceHeadGlue context value'
          Evaluation.applySpine value'' spine

        (Domain.Lit lit, Syntax.LiteralBranches literalBranches) -> do
          value' <- Evaluation.chooseLiteralBranch branchEnv lit literalBranches defaultBranch
          value'' <- forceHeadGlue context value'
          Evaluation.applySpine value'' spine

        _ ->
          pure $ Domain.Neutral (Domain.Case scrutinee' branches) spine

    _ ->
      pure value

instantiateType
  :: Context v
  -> Domain.Type
  -> [(Plicity, Domain.Value)]
  -> M Domain.Type
instantiateType context type_ spine = do
  type' <- Context.forceHead context type_
  case (type', spine) of
    (_, []) ->
      pure type'

    (Domain.Fun _ plicity1 target, (plicity2, _):spine')
      | plicity1 == plicity2 ->
      instantiateType context target spine'

    (Domain.Pi _ _ plicity1 targetClosure, (plicity2, arg):spine')
      | plicity1 == plicity2 -> do
        target <- Evaluation.evaluateClosure targetClosure arg
        instantiateType context target spine'

    _ ->
      panic "instantiateType"

-------------------------------------------------------------------------------
-- Error reporting

report :: Context v -> Error.Elaboration -> M ()
report context err =
  let
    err' =
      Error.Elaboration (scopeKey context) $
      Error.Spanned (span context) err
  in
  atomicModifyIORef (errors context) $ \errs ->
    (errs Tsil.:> err', ())

reportParseError :: Context v -> Error.Parsing -> M ()
reportParseError context err = do
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      Context.scopeKey context

  maybeFilePath <- fetch $ Query.ModuleFile module_
  forM_ maybeFilePath $ \filePath -> do
    let
      err' =
        Error.Parse filePath err
    atomicModifyIORef (errors context) $ \errs ->
      (errs Tsil.:> err', ())

try :: Context v -> M a -> M (Maybe a)
try context m =
  (Just <$> m) `catch` \err -> do
    report context err
    pure Nothing

try_ :: Context v -> M () -> M Bool
try_ context m =
  (True <$ m) `catch` \err -> do
    report context err
    pure False


-------------------------------------------------------------------------------
-- Zonking
zonk
  :: Context v
  -> Syntax.Term v
  -> M (Syntax.Term v)
zonk context term = do
  metaVars <- newIORef mempty
  Zonking.zonkTerm (Context.toEnvironment context) (go metaVars) term
  where
    go metaVars index = do
      indexMap <- readIORef metaVars
      case IntMap.lookup index indexMap of
        Nothing -> do
          solution <- Context.lookupMeta index context
          case solution of
            Meta.Unsolved _ _ -> do
              atomicModifyIORef metaVars $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Meta.Solved term' _ -> do
              term'' <- Zonking.zonkTerm (Environment.empty $ Context.scopeKey context) (go metaVars) term'
              atomicModifyIORef metaVars $ \indexMap' ->
                (IntMap.insert index (Just term'') indexMap', ())
              pure $ Just term''

        Just solution ->
          pure solution
