{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
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
import qualified Elaboration.Postponed as Postponed
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
import Telescope (Telescope)
import qualified Telescope
import Var

data Context v = Context
  { scopeKey :: !Scope.KeyedName
  , span :: !Span.Relative
  , indices :: Index.Map v Var
  , surfaceNames :: HashMap Name.Surface (Domain.Value, Domain.Type)
  , varNames :: IntMap Var Name
  , values :: IntMap Var Domain.Value
  , types :: IntMap Var Domain.Type
  , boundVars :: IntSeq Var
  , metas :: !(IORef Meta.Vars)
  , postponed :: !(IORef Postponed.Checks)
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

empty :: MonadBase IO m => Scope.KeyedName -> m (Context Void)
empty key = do
  ms <- newIORef Meta.empty
  es <- newIORef mempty
  ps <- newIORef Postponed.empty
  pure Context
    { scopeKey = key
    , span = Span.Relative 0 0
    , surfaceNames = mempty
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
    , surfaceNames = mempty
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

spanned :: Span.Relative -> Context v -> Context v
spanned s context =
  context
    { span = s
    }

-------------------------------------------------------------------------------
-- Extension

extendSurface
  :: Context v
  -> Name.Surface
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendSurface context name@(Name.Surface nameText) type_ = do
  var <- freshVar
  pure
    ( context
      { surfaceNames = HashMap.insert name (Domain.var var, type_) $ surfaceNames context
      , varNames = IntMap.insert var (Name nameText) $ varNames context
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

extendSurfaceDef
  :: Context v
  -> Name.Surface
  -> Domain.Value
  -> Domain.Type
  -> M (Context (Succ v), Var)
extendSurfaceDef context surfaceName@(Name.Surface nameText) value type_ = do
  var <- freshVar
  pure
    ( context
      { surfaceNames = HashMap.insert surfaceName (Domain.var var, type_) $ surfaceNames context
      , varNames = IntMap.insert var (Name nameText) $ varNames context
      , indices = indices context Index.Map.:> var
      , values = IntMap.insert var value (values context)
      , types = IntMap.insert var type_ (types context)
      }
    , var
    )

withSurfaceNameValue :: Name.Surface -> Domain.Value -> Domain.Type -> Context v -> Context v
withSurfaceNameValue name value type_ context =
  context
    { surfaceNames = HashMap.insert name (value, type_) $ surfaceNames context
    }

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

    Domain.Fun domain _ target -> do
      domainVars <- dependencies context domain
      targetVars <- dependencies context target
      pure $ domainVars <> targetVars

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

-------------------------------------------------------------------------------
-- Lookup

lookupSurfaceName :: Name.Surface -> Context v -> Maybe (Domain.Value, Domain.Type)
lookupSurfaceName surfaceName context =
  HashMap.lookup surfaceName (surfaceNames context)

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

-------------------------------------------------------------------------------
-- Prettyable terms

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

-------------------------------------------------------------------------------
-- Meta variables

newMeta :: Context v -> Domain.Type -> M Domain.Value
newMeta context type_ = do
  (closedType, arity) <- piBoundVars context type_
  i <- atomicModifyIORef' (metas context) $ Meta.insert closedType arity (span context)
  pure $ Domain.Neutral (Domain.Meta i) $ Domain.Apps ((,) Explicit . Domain.var <$> IntSeq.toTsil (boundVars context))

newMetaType :: Context v -> M Domain.Value
newMetaType context =
  newMeta context Builtin.Type

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void, Int)
piBoundVars context type_ = do
  let
    arity =
      IntSeq.size $ boundVars context
  type' <-
    Readback.readback
      Environment
        { scopeKey = scopeKey context
        , indices = Index.Map $ boundVars context
        , values = values context
        , glueableBefore = Index arity
        }
      type_

  piType <- pis (boundVars context) type'
  pure (piType, arity)
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
  :: Context v
  -> Meta.Index
  -> M Meta.Var
lookupMeta context i = do
  m <- readIORef (metas context)
  pure $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context meta term = do
  (arity, unblocked) <- atomicModifyIORef' (metas context) $ Meta.solve meta term
  if IntSet.null unblocked then
    pure ()
  else do
    let
      emptyContext =
        emptyFrom context
    value <- Evaluation.evaluate (toEnvironment emptyContext) term
    maybeNewBlockingMeta <- stillBlocked emptyContext arity value
    case maybeNewBlockingMeta of
      Nothing ->
        checkUnblockedPostponedChecks context unblocked

      Just newBlockingMeta ->
        addPostponementsBlockedOnMeta context unblocked newBlockingMeta

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
      meta <- lookupMeta context metaIndex

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
      meta <- lookupMeta context metaIndex

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
          solution <- lookupMeta context index
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
            Postponed.Unchecked {} -> do
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Postponed.Checking -> do
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index Nothing indexMap', ())
              pure Nothing

            Postponed.Checked term' -> do
              term'' <- Zonking.zonkTerm env zonkMeta zonkPostponed $ Syntax.coerce term'
              atomicModifyIORef' postponedRef $ \indexMap' ->
                (IntMap.insert index (Just $ Syntax.coerce term'') indexMap', ())
              pure $ Just term''

        Just solution ->
          pure $ Syntax.fromVoid <$> solution
  Zonking.zonkTerm (toEnvironment context) zonkMeta zonkPostponed term

-------------------------------------------------------------------------------
-- Postponement

stillBlocked :: Context v -> Int -> Domain.Value -> M (Maybe Meta.Index)
stillBlocked context !arity value = do
  value' <- forceHead context value
  case value' of
    Domain.Neutral (Domain.Meta blockingMeta) _ ->
      pure $ Just blockingMeta

    Domain.Lam bindings domain _ closure
      | arity > 0 -> do
        (context', var) <- extend context (Bindings.toName bindings) domain
        target <- Evaluation.evaluateClosure closure $ Domain.var var
        stillBlocked context' (arity - 1) target

    _ ->
      pure Nothing

newPostponedCheck :: Context v -> Meta.Index -> (Postponement.CanPostpone -> M (Syntax.Term v)) -> M Postponement.Index
newPostponedCheck context blockingMeta check = do
  postponementIndex <- atomicModifyIORef' (postponed context) $ Postponed.insert check
  addPostponementBlockedOnMeta context postponementIndex blockingMeta
  pure postponementIndex

addPostponementBlockedOnMeta :: Context v -> Postponement.Index -> Meta.Index -> M ()
addPostponementBlockedOnMeta context postponementIndex blockingMeta =
  atomicModifyIORef' (metas context) $ \m -> (Meta.addPostponedIndex blockingMeta postponementIndex m, ())

addPostponementsBlockedOnMeta :: Context v -> IntSet Postponement.Index -> Meta.Index -> M ()
addPostponementsBlockedOnMeta context postponementIndices blockingMeta =
  atomicModifyIORef' (metas context) $ \m -> (Meta.addPostponedIndices blockingMeta postponementIndices m, ())

lookupPostponedCheck
  :: Postponement.Index
  -> Context v
  -> M Postponed.Check
lookupPostponedCheck i context =
  Postponed.lookup i <$> readIORef (postponed context)

checkUnblockedPostponedChecks :: Context v -> IntSet Postponement.Index -> M ()
checkUnblockedPostponedChecks context indices_ = do
  forM_ (IntSet.toList indices_) $ \index -> do
    join $ atomicModifyIORef' (postponed context) $ \postponed' -> do
      let
        (doIt, postponed'') =
          Postponed.adjustF adjust index postponed'

        adjust check =
          case check of
            Postponed.Unchecked check' ->
              ( do
                result <- check' Postponement.CanPostpone
                atomicModifyIORef' (postponed context) $ \p' ->
                  (Postponed.update index (Postponed.Checked result) p', ())
              , check
              )

            Postponed.Checking ->
              (pure (), check)

            Postponed.Checked _ ->
              (pure (), check)
      (postponed'', doIt)

inferAllPostponedChecks :: Context v -> M ()
inferAllPostponedChecks context = do
  go 0
  where
    go index =
      join $ atomicModifyIORef' (postponed context) $ \postponed' ->
        if index < Postponed.nextIndex postponed' then do
          let
            (doIt, postponed'') =
              Postponed.adjustF adjust index postponed'

            adjust value =
              case value of
                Postponed.Unchecked check ->
                  ( do
                    result <- check Postponement.Can'tPostpone
                    atomicModifyIORef' (postponed context) $ \p' ->
                      (Postponed.update index (Postponed.Checked result) p', ())
                  , Postponed.Checking
                  )

                Postponed.Checking ->
                  (pure (), value)

                Postponed.Checked _ ->
                  (pure (), value)

          (postponed'', do doIt; go $ index + 1)

        else
          (postponed', pure ())
