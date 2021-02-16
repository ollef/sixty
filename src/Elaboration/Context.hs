{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TupleSections #-}
module Elaboration.Context where

import Protolude hiding (IntMap, IntSet, catch, check, force)

import Control.Exception.Lifted
import Control.Monad.Base
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef.Lifted
import Rock

import qualified Builtin
import qualified Core.Binding as Binding
import qualified Core.Bindings as Bindings
import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import Core.Domain.Pattern (Pattern)
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import qualified Core.Zonking as Zonking
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Elaboration.Meta as Meta
import Environment (Environment(Environment))
import qualified Environment
import Error (Error)
import qualified Error
import qualified Error.Parsing as Error
import Index
import qualified Index.Map
import qualified Index.Map as Index
import Literal (Literal)
import qualified Meta
import Monad
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Postponement
import qualified Query
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import Telescope (Telescope)
import qualified Telescope
import Var

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , span :: !Span.Relative
  , indices :: Index.Map v Var
  , nameVars :: HashMap Name Var
  , varNames :: IntMap Var Name
  , values :: IntMap Var Domain.Value
  , types :: IntMap Var Domain.Type
  , boundVars :: IntSeq Var
  , metas :: !(IORef Meta.Vars)
  , postponed :: !(IORef PostponedChecks)
  , coveredConstructors :: CoveredConstructors
  , coveredLiterals :: CoveredLiterals
  , errors :: !(IORef (Tsil Error))
  }

type CoveredConstructors = IntMap Var (HashSet Name.QualifiedConstructor)

type CoveredLiterals = IntMap Var (HashSet Literal)

toEnvironment
  :: Context v
  -> Domain.Environment v
toEnvironment context =
  Environment
    { scopeKey = scopeKey context
    , indices = indices context
    , values = values context
    , glueableBefore = Index.zero
    }

toPrettyableTerm :: Context v -> Syntax.Term v -> M Error.PrettyableTerm
toPrettyableTerm context term = do
  term' <- zonk context term
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      scopeKey context
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
      scopeKey context
  pure $ Error.PrettyableTerm module_ mempty (Syntax.coerce term')

toPrettyablePattern :: Context v -> Pattern -> Error.PrettyablePattern
toPrettyablePattern context = do
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      scopeKey context
  Error.PrettyablePattern
    module_
    ((`lookupVarName` context) <$> toList (indices context))

empty :: MonadBase IO m => Scope.KeyedName -> m (Context Void)
empty key = do
  ms <- newIORef Meta.empty
  es <- newIORef mempty
  ps <- newIORef PostponedChecks { checks = mempty, nextIndex = 0 }
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
    , postponed = ps
    , errors = es
    , coveredConstructors = mempty
    , coveredLiterals = mempty
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
    , postponed = postponed context
    , errors = errors context
    , coveredConstructors = mempty
    , coveredLiterals = mempty
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
  value' <- lift $ forceHeadGlue context value
  case value' of
    Domain.Neutral hd spine -> do
      hdVars <- headVars hd
      elimVars <- Domain.mapM eliminationDependencies spine
      pure $ hdVars <> fold elimVars

    Domain.Con _ args ->
      fold <$> mapM (dependencies context . snd) args

    Domain.Lit _ ->
      pure mempty

    Domain.Glued (Domain.Global _) spine _ ->
      fold <$> Domain.mapM eliminationDependencies spine

    Domain.Glued _ _ value'' -> do
      value''' <- lift $ force value''
      dependencies context value'''

    Domain.Lam bindings type' _ closure ->
      abstractionDependencies (Bindings.toName bindings) type' closure

    Domain.Pi binding type' _ closure ->
      abstractionDependencies (Binding.toName binding) type' closure

  where
    eliminationDependencies elimination =
      case elimination of
        Domain.App _plicity arg ->
          dependencies context arg

        Domain.Case (Domain.Branches env branches defaultBranch) -> do
          defaultBranchVars <- mapM (dependencies context <=< lift . Evaluation.evaluate env) defaultBranch
          brVars <- branchVars context env branches
          pure $ fold defaultBranchVars <> brVars

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
  fromMaybe (panic $ "Context.lookupVarType " <> show var)
    $ IntMap.lookup var
    $ types context

lookupVarValue :: Var -> Context v -> Maybe Domain.Type
lookupVarValue var context =
  IntMap.lookup var (values context)

newMeta :: Domain.Type -> Context v -> M Domain.Value
newMeta type_ context = do
  closedType <- piBoundVars context type_
  i <- atomicModifyIORef' (metas context) $ Meta.insert closedType (span context)
  pure $ Domain.Neutral (Domain.Meta i) $ Domain.Apps ((,) Explicit . Domain.var <$> IntSeq.toTsil (boundVars context))

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
        , glueableBefore = Index $ IntSeq.size $ boundVars context
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
                , glueableBefore = Index $ IntSeq.size vars'
                }
              varType
          let
            term' = Syntax.Pi (Binding.Unspanned $ lookupVarName var context) varType' Explicit $ Syntax.succ term
          pis vars' term'

lookupMeta
  :: Meta.Index
  -> Context v
  -> M Meta.Var
lookupMeta i context = do
  m <- readIORef (metas context)
  pure $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context i term = do
  unblocked <- atomicModifyIORef' (metas context) $ Meta.solve i term
  unblockPostponedChecks context unblocked

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
      | Just headValue <- lookupVarValue var context -> do
        value' <- Evaluation.applySpine headValue spine
        forceHead context value'

    Domain.Neutral (Domain.Meta metaIndex) spine -> do
      meta <- lookupMeta metaIndex context

      case meta of
        Meta.Solved headValue _ -> do
          headValue' <- Evaluation.evaluate (Environment.empty $ scopeKey context) headValue
          value' <- Evaluation.applySpine headValue' spine
          forceHead context value'

        Meta.Unsolved {} ->
          pure value

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
      | Just headValue <- lookupVarValue var context -> do
        value' <- lazy $ do
          value' <- Evaluation.applySpine headValue spine
          forceHeadGlue context value'
        pure $ Domain.Glued (Domain.Var var) spine value'

    Domain.Neutral (Domain.Meta metaIndex) spine -> do
      meta <- lookupMeta metaIndex context

      case meta of
        Meta.Solved headValue _ -> do
          value' <- lazy $ do
            headValue' <- Evaluation.evaluate (Environment.empty $ scopeKey context) headValue
            value' <- Evaluation.applySpine headValue' spine
            forceHeadGlue context value'
          pure $ Domain.Glued (Domain.Meta metaIndex) spine value'

        Meta.Unsolved {} ->
          pure value

    _ ->
      pure value

instantiateType
  :: Context v
  -> Domain.Type
  -> [(Plicity, Domain.Value)]
  -> M Domain.Type
instantiateType context type_ spine = do
  type' <- forceHead context type_
  case (type', spine) of
    (_, []) ->
      pure type'

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
  atomicModifyIORef' (errors context) $ \errs ->
    (errs Tsil.:> err', ())

reportParseError :: Context v -> Error.Parsing -> M ()
reportParseError context err = do
  let
    Scope.KeyedName _ (Name.Qualified module_ _) =
      scopeKey context

  maybeFilePath <- fetch $ Query.ModuleFile module_
  forM_ maybeFilePath $ \filePath -> do
    let
      err' =
        Error.Parse filePath err
    atomicModifyIORef' (errors context) $ \errs ->
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
  metasRef <- newIORef mempty
  postponedRef <- newIORef (mempty :: IntMap Postponement.Index (Maybe (Syntax.Term Void)))
  let
    zonkMeta index = do
      indexMap <- readIORef metasRef
      case IntMap.lookup index indexMap of
        Nothing -> do
          solution <- lookupMeta index context
          case solution of
            Meta.Unsolved {} -> do
              atomicModifyIORef' metasRef $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Meta.Solved term' _ -> do
              term'' <- Zonking.zonkTerm (Environment.empty $ scopeKey context) zonkMeta zonkPostponed term'
              atomicModifyIORef' metasRef $ \indexMap' ->
                (IntMap.insert index (Just term'') indexMap', ())
              pure $ Just term''

        Just solution ->
          pure solution

    zonkPostponed :: Domain.Environment v -> Postponement.Index -> M (Maybe (Syntax.Term v))
    zonkPostponed env index = do
      indexMap <- readIORef postponedRef
      case IntMap.lookup index indexMap of
        Nothing -> do
          solution <- lookupPostponedCheck index context
          case solution of
            Unchecked {} -> do
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Checking -> do
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Checked term' -> do
              term'' <- Zonking.zonkTerm env zonkMeta zonkPostponed $ Syntax.coerce term'
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index (Just $ Syntax.coerce term'') indexMap', ())
              pure $ Just term''

        Just solution ->
          pure $ Syntax.fromVoid <$> solution
  Zonking.zonkTerm (toEnvironment context) zonkMeta zonkPostponed term

-------------------------------------------------------------------------------
-- Postponement
data Postponed where
  Unchecked :: Context v -> Domain.Type -> (CanPostpone -> M (Syntax.Term v)) -> Postponed
  Checking :: Postponed
  Checked :: Syntax.Term v -> Postponed

data PostponedChecks = PostponedChecks
  { checks :: !(IntMap Postponement.Index Postponed)
  , nextIndex :: !Postponement.Index
  }

data CanPostpone
  = Can'tPostpone
  | CanPostpone
  deriving Show

newPostponedCheck :: Context v -> Meta.Index -> Domain.Type -> (CanPostpone -> M (Syntax.Term v)) -> M Postponement.Index
newPostponedCheck context blockingMeta type_ check = do
  postponementIndex <- atomicModifyIORef' (postponed context) $ \p ->
    (PostponedChecks (IntMap.insert (nextIndex p) (Unchecked context type_ check) (checks p)) (nextIndex p + 1), nextIndex p)
  addPostponementBlockedOnMeta context postponementIndex blockingMeta
  pure postponementIndex

addPostponementBlockedOnMeta :: Context v -> Postponement.Index -> Meta.Index -> M ()
addPostponementBlockedOnMeta context postponementIndex blockingMeta =
  atomicModifyIORef' (metas context) $ \m -> (Meta.addPostponedIndex blockingMeta postponementIndex m, ())

lookupPostponedCheck
  :: Postponement.Index
  -> Context v
  -> M Postponed
lookupPostponedCheck i context = do
  p <- readIORef (postponed context)
  pure $ checks p IntMap.! i

unblockPostponedChecks :: Context v -> IntSet Postponement.Index -> M ()
unblockPostponedChecks context indices_ =
  forM_ (IntSet.toList indices_) $ \index -> do
    p <- readIORef $ postponed context
    case checks p IntMap.! index of
      Unchecked context' type_ check -> do
        do
          type' <- forceHead context' type_
          case type' of
            Domain.Neutral (Domain.Meta newBlockingMeta) _ -> do
              addPostponementBlockedOnMeta context index newBlockingMeta
              atomicModifyIORef' (postponed context) $ \p' ->
                (PostponedChecks (IntMap.insert index (Unchecked context' type' check) (checks p')) (nextIndex p'), ())

            _ -> do
              result <- check CanPostpone
              atomicModifyIORef' (postponed context) $ \p' ->
                (PostponedChecks (IntMap.insert index (Checked result) (checks p')) (nextIndex p'), ())

      Checking ->
        pure ()

      Checked _ ->
        pure ()

inferAllPostponedChecks :: Context v -> M ()
inferAllPostponedChecks context = do
  go 0
  where
    go index = do
      p <- readIORef $ postponed context
      if index < nextIndex p then do
        case checks p IntMap.! index of
          Unchecked _ _ check -> do
            atomicModifyIORef' (postponed context) $ \p' ->
              (PostponedChecks (IntMap.insert index Checking (checks p')) (nextIndex p'), ())
            result <- check Can'tPostpone
            atomicModifyIORef' (postponed context) $ \p' ->
              (PostponedChecks (IntMap.insert index (Checked result) (checks p')) (nextIndex p'), ())

          Checking ->
            pure ()

          Checked _ ->
            pure ()
        go $ index + 1
      else
        pure ()
