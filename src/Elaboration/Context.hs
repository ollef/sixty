{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}

module Elaboration.Context (
  module Elaboration.Context,
  module Elaboration.Context.Type,
) where

import qualified Builtin
import Control.Exception.Lifted
import Control.Monad.Base
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import Core.Domain.Pattern (Pattern)
import qualified Core.Evaluation as Evaluation
import qualified Core.Readback as Readback
import qualified Core.Syntax as Syntax
import qualified Core.Zonking as Zonking
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IORef.Lifted
import qualified Data.IntSeq as IntSeq
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Tsil as Tsil
import Elaboration.Context.Type
import qualified Elaboration.Meta as Meta
import qualified Elaboration.Postponed as Postponed
import {-# SOURCE #-} Elaboration.Unification as Unification
import Environment (Environment (Environment))
import qualified Environment
import qualified Error
import qualified Error.Hydrated as Error
import qualified Error.Parsing as Error
import Index
import qualified Index.Map
import Literal (Literal)
import qualified Meta
import Monad
import Name (Name (Name))
import qualified Name
import Plicity
import qualified Postponement
import Prettyprinter (Doc)
import qualified Prettyprinter.Render.Text as Prettyprinter
import Protolude hiding (catch, check, force, moduleName, state)
import qualified Query
import Rock
import qualified Scope
import qualified Span
import Telescope (Telescope)
import qualified Telescope
import Var

moduleName :: Context v -> Name.Module
moduleName context = context.definitionName.moduleName

toEnvironment
  :: Context v
  -> Domain.Environment v
toEnvironment context =
  Environment
    { indices = context.indices
    , values = context.values
    , glueableBefore = Index.Zero
    }

empty :: (MonadBase IO m) => Scope.DefinitionKind -> Name.Qualified -> m (Context Void)
empty definitionKind definitionName = do
  ms <- newIORef Meta.empty
  es <- newIORef mempty
  ps <- newIORef Postponed.empty
  cs <- newIORef mempty
  pure
    Context
      { definitionKind
      , definitionName
      , definitionType = Nothing
      , span = Span.Relative 0 0
      , surfaceNames = mempty
      , varNames = mempty
      , indices = Index.Map.Empty
      , types = mempty
      , boundVars = mempty
      , metas = ms
      , postponed = ps
      , values = mempty
      , equal = mempty
      , notEqual = mempty
      , coverageChecks = cs
      , errors = es
      }

emptyFrom :: Context v -> Context Void
emptyFrom context =
  Context
    { definitionKind = context.definitionKind
    , definitionName = context.definitionName
    , definitionType = context.definitionType
    , span = context.span
    , surfaceNames = mempty
    , varNames = mempty
    , indices = Index.Map.Empty
    , types = mempty
    , boundVars = mempty
    , metas = context.metas
    , postponed = context.postponed
    , values = mempty
    , equal = mempty
    , notEqual = mempty
    , coverageChecks = context.coverageChecks
    , errors = context.errors
    }

spanned :: Span.Relative -> Context v -> Context v
spanned s context =
  context
    { span = s
    }

-------------------------------------------------------------------------------
coveredConstructorsAndLiterals :: Context v -> Domain.Head -> Domain.Spine -> M (HashSet Name.QualifiedConstructor, HashSet Literal)
coveredConstructorsAndLiterals context head_ spine =
  case HashMap.lookup head_ context.notEqual of
    Nothing -> pure mempty
    Just spines ->
      fold
        <$> mapM
          ( \(spine', constructors, literals) -> do
              eq <- Unification.equalSpines context spine spine'
              pure if eq then (constructors, literals) else mempty
          )
          spines

coveredConstructors :: Context v -> Domain.Head -> Domain.Spine -> M (HashSet Name.QualifiedConstructor)
coveredConstructors context head_ spine = fst <$> coveredConstructorsAndLiterals context head_ spine

coveredLiterals :: Context v -> Domain.Head -> Domain.Spine -> M (HashSet Literal)
coveredLiterals context head_ spine = snd <$> coveredConstructorsAndLiterals context head_ spine

withCoveredConstructors :: Context v -> Domain.Head -> Domain.Spine -> HashSet Name.QualifiedConstructor -> Context v
withCoveredConstructors context head_ spine constructors =
  context
    { notEqual =
        HashMap.insertWith (<>) head_ [(spine, constructors, mempty)] context.notEqual
    }

withCoveredLiterals :: Context v -> Domain.Head -> Domain.Spine -> HashSet Literal -> Context v
withCoveredLiterals context head_ spine literals =
  context
    { notEqual =
        HashMap.insertWith
          (<>)
          head_
          [(spine, mempty, literals)]
          context.notEqual
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
        { surfaceNames = HashMap.insert name (Domain.var var, type_) context.surfaceNames
        , varNames = EnumMap.insert var (Name nameText) context.varNames
        , indices = context.indices Index.Map.:> var
        , types = EnumMap.insert var type_ context.types
        , boundVars = context.boundVars IntSeq.:> var
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
        { varNames = EnumMap.insert var name context.varNames
        , indices = context.indices Index.Map.:> var
        , types = EnumMap.insert var type_ context.types
        , boundVars = context.boundVars IntSeq.:> var
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
        { surfaceNames = HashMap.insert surfaceName (Domain.var var, type_) context.surfaceNames
        , varNames = EnumMap.insert var (Name nameText) context.varNames
        , indices = context.indices Index.Map.:> var
        , values = EnumMap.insert var value context.values
        , types = EnumMap.insert var type_ context.types
        }
    , var
    )

withSurfaceNameValue :: Name.Surface -> Domain.Value -> Domain.Type -> Context v -> Context v
withSurfaceNameValue name value type_ context =
  context
    { surfaceNames = HashMap.insert name (value, type_) context.surfaceNames
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
        { varNames = EnumMap.insert var name context.varNames
        , indices = context.indices Index.Map.:> var
        , values = EnumMap.insert var value context.values
        , types = EnumMap.insert var type_ context.types
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
        { varNames = EnumMap.insert var (Bindings.toName binding) context.varNames
        , indices = context.indices Index.Map.:> var
        , types = EnumMap.insert var type_ context.types
        , boundVars =
            case IntSeq.elemIndex beforeVar context.boundVars of
              Nothing -> panic "extendBefore no such var"
              Just i -> IntSeq.insertAt i var context.boundVars
        }
    , var
    )

defineWellOrdered :: Context v -> Var -> Domain.Value -> Context v
defineWellOrdered context var value =
  context
    { values = EnumMap.insert var value context.values
    , boundVars = IntSeq.delete var context.boundVars
    }

rewrite :: Context v -> Domain.Head -> Domain.Spine -> Domain.Value -> Context v
rewrite context head_ spine value =
  context
    { equal = HashMap.insertWith (<>) head_ [(spine, value)] context.equal
    }

define :: Context v -> Domain.Head -> Domain.Spine -> Domain.Value -> M (Context v)
define context (Domain.Var var) Domain.Empty value = do
  -- putText "define"
  -- dumpValue context (Domain.Neutral head_ spine)
  -- dumpValue context value
  deps <- evalStateT (freeVars context value) mempty
  let context' = defineWellOrdered context var value
      context''
        | EnumSet.null deps = context'
        | otherwise =
            context'
              { boundVars =
                  IntSeq.fromTsil pre <> IntSeq.fromTsil post
              }
      (pre, post) = Tsil.partition (`EnumSet.member` deps) $ IntSeq.toTsil context'.boundVars
  pure context''
define context head_ spine value =
  pure $ rewrite context head_ spine value

skip :: Context v -> M (Context (Succ v))
skip context = do
  (context', _) <- extendDef context "skip" Builtin.Type Builtin.Type
  pure context'

-- TODO: Move
freeVars
  :: Context v
  -> Domain.Value
  -> StateT (EnumMap Var (EnumSet Var)) M (EnumSet Var)
freeVars context value = do
  value' <- lift $ forceHeadGlue context value
  case value' of
    Domain.AnyNeutral hd spine -> do
      hdVars <- headVars hd
      elimVars <- Domain.mapM eliminationVars spine
      pure $ hdVars <> fold elimVars
    Domain.Con _ args ->
      fold <$> mapM (freeVars context . snd) args
    Domain.Lit _ ->
      pure mempty
    Domain.Glued (Domain.Global _) spine _ ->
      fold <$> Domain.mapM eliminationVars spine
    Domain.Glued _ _ value'' ->
      freeVars context value''
    Domain.Lazy lazyValue -> do
      value'' <- lift $ force lazyValue
      freeVars context value''
    Domain.Lam bindings type' _ closure ->
      abstractionVars (Bindings.toName bindings) type' closure
    Domain.Pi binding type' _ closure ->
      abstractionVars (Binding.toName binding) type' closure
    Domain.Fun domain _ target -> do
      domainVars <- freeVars context domain
      targetVars <- freeVars context target
      pure $ domainVars <> targetVars
  where
    eliminationVars elimination =
      case elimination of
        Domain.App _plicity arg ->
          freeVars context arg
        Domain.Case (Domain.Branches env branches defaultBranch) -> do
          defaultBranchVars <- mapM (freeVars context <=< lift . Evaluation.evaluate env) defaultBranch
          brVars <- branchVars context env branches
          pure $ fold defaultBranchVars <> brVars

    abstractionVars name type' closure = do
      typeVars <- freeVars context type'
      (context', var) <- lift $ extend context name type'
      body <- lift $ Evaluation.evaluateClosure closure $ Domain.var var
      bodyVars <- freeVars context' body
      pure $ typeVars <> EnumSet.delete var bodyVars

    headVars hd =
      case hd of
        Domain.Var v
          | v `IntSeq.member` context.boundVars -> do
              cache <- get
              typeDeps <- case EnumMap.lookup v cache of
                Nothing -> do
                  typeDeps <- freeVars context $ lookupVarType v context
                  modify $ EnumMap.insert v typeDeps
                  pure typeDeps
                Just typeDeps ->
                  pure typeDeps

              pure $ typeDeps <> EnumSet.singleton v
          | otherwise ->
              pure $ EnumSet.singleton v
        Domain.Global _ ->
          pure mempty
        Domain.Meta _ ->
          pure mempty

    branchVars
      :: Context v
      -> Domain.Environment v'
      -> Syntax.Branches v'
      -> StateT (EnumMap Var (EnumSet Var)) M (EnumSet Var)
    branchVars context' env branches =
      fold
        <$> case branches of
          Syntax.ConstructorBranches _ constructorBranches ->
            mapM (telescopeVars context' env . snd) $ toList constructorBranches
          Syntax.LiteralBranches literalBranches ->
            forM (toList literalBranches) \(_, branch) -> do
              branch' <- lift $ Evaluation.evaluate env branch
              freeVars context' branch'

    telescopeVars
      :: Context v
      -> Domain.Environment v'
      -> Telescope Bindings Syntax.Type Syntax.Term v'
      -> StateT (EnumMap Var (EnumSet Var)) M (EnumSet Var)
    telescopeVars context' env tele =
      case tele of
        Telescope.Empty body -> do
          body' <- lift $ Evaluation.evaluate env body
          freeVars context' body'
        Telescope.Extend binding domain _ tele' -> do
          domain' <- lift $ Evaluation.evaluate env domain
          domainVars <- freeVars context' domain'
          (context'', var) <- lift $ extend context' (Bindings.toName binding) domain'
          let env' =
                Environment.extendVar env var

          rest <- telescopeVars context'' env' tele'
          pure $ domainVars <> EnumSet.delete var rest

-------------------------------------------------------------------------------
-- Lookup

lookupSurfaceName :: Name.Surface -> Context v -> Maybe (Domain.Value, Domain.Type)
lookupSurfaceName surfaceName context =
  HashMap.lookup surfaceName context.surfaceNames

lookupVarIndex :: Var -> Context v -> Maybe (Index v)
lookupVarIndex var context =
  Index.Map.elemIndex var context.indices

lookupVarName :: Var -> Context v -> Name
lookupVarName var context =
  EnumMap.findWithDefault (panic "Context.lookupVarName") var context.varNames

lookupIndexVar :: Index v -> Context v -> Var
lookupIndexVar index context =
  Index.Map.index context.indices index

lookupIndexType :: Index v -> Context v -> Domain.Type
lookupIndexType index context =
  lookupVarType (lookupIndexVar index context) context

lookupVarType :: Var -> Context v -> Domain.Type
lookupVarType var context =
  EnumMap.findWithDefault (panic $ "Context.lookupVarType " <> show var) var context.types

-------------------------------------------------------------------------------
-- Prettyable terms

prettyTerm :: Context v -> Syntax.Term v -> M (Doc ann)
prettyTerm context term = do
  pt <- toPrettyableTerm context term
  Error.prettyPrettyableTerm 0 pt

dumpTerm :: Context v -> Syntax.Term v -> M ()
dumpTerm context term = do
  term' <- zonk context term
  doc <- prettyTerm context term'
  liftIO $ Prettyprinter.putDoc doc

prettyValue :: Context v -> Domain.Value -> M (Doc ann)
prettyValue context term = do
  pt <- toPrettyableValue context term
  Error.prettyPrettyableTerm 0 pt

dumpValue :: Context v -> Domain.Value -> M ()
dumpValue context value = do
  let env = toEnvironment context
  term <- Readback.readback env value
  dumpTerm context term
  putText ""
  unless (HashMap.null context.equal && EnumMap.null context.values) $
    putText "  where"
  forM_ (EnumMap.toList context.values) \(var, value') -> do
    lhsTerm <- Readback.readback env (Domain.Neutral (Domain.Var var) mempty)
    rhsTerm <- Readback.readback env value'
    putStr ("    " :: Text)
    dumpTerm context lhsTerm
    putStr (" = " :: Text)
    dumpTerm context rhsTerm
    putText ""
  forM_ (HashMap.toList context.equal) \(head_, argValues) ->
    forM_ argValues \(spine, eqValue) -> do
      lhsTerm <- Readback.readback env (Domain.Neutral head_ spine)
      rhsTerm <- Readback.readback env eqValue
      putStr ("    " :: Text)
      dumpTerm context lhsTerm
      putStr (" = " :: Text)
      dumpTerm context rhsTerm
      putText ""

toPrettyableTerm :: Context v -> Syntax.Term v -> M Error.PrettyableTerm
toPrettyableTerm context term = do
  term' <- zonk context term
  pure $
    Error.PrettyableTerm
      (moduleName context)
      ((`lookupVarName` context) <$> toList context.indices)
      (Syntax.coerce term')

toPrettyableValue :: Context v -> Domain.Value -> M Error.PrettyableTerm
toPrettyableValue context value = do
  term <- Readback.readback (toEnvironment context) value
  toPrettyableTerm context term

toPrettyableClosedTerm :: Context v -> Syntax.Term Void -> M Error.PrettyableTerm
toPrettyableClosedTerm context term = do
  term' <- zonk (emptyFrom context) term
  pure $ Error.PrettyableTerm (moduleName context) mempty (Syntax.coerce term')

toPrettyablePattern :: Context v -> Pattern -> Error.PrettyablePattern
toPrettyablePattern context = do
  Error.PrettyablePattern
    (moduleName context)
    ((`lookupVarName` context) <$> toList context.indices)

-------------------------------------------------------------------------------
-- Meta variables

newMeta :: Context v -> Domain.Type -> M Domain.Value
newMeta context type_ = do
  (_, _, value) <- newMetaReturningIndex context type_
  pure value

newMetaType :: Context v -> M Domain.Value
newMetaType context =
  newMeta context Builtin.Type

newMetaReturningIndex :: Context v -> Domain.Type -> M (Meta.Index, Seq (Plicity, Var), Domain.Value)
newMetaReturningIndex context type_ = do
  (closedType, arity) <- piBoundVars context type_
  i <- atomicModifyIORef' context.metas $ Meta.new closedType arity context.span
  let args =
        (,) Explicit <$> IntSeq.toSeq context.boundVars
  pure (i, args, Domain.Neutral (Domain.Meta i) $ Domain.Apps (second Domain.var <$> args))

piBoundVars :: Context v -> Domain.Type -> M (Syntax.Type Void, Int)
piBoundVars context type_ = do
  let arity = IntSeq.length context.boundVars
  piType <-
    varPis
      context
      -- TODO
      (toEnvironment context) {Environment.indices = Index.Map.Empty, Environment.glueableBefore = Index.Zero}
      ((Explicit,) <$> toList context.boundVars)
      type_
  pure (piType, arity)

varPis
  :: Context v
  -> Domain.Environment v'
  -> [(Plicity, Var)]
  -> Domain.Value
  -> M (Syntax.Term v')
varPis context env vars target =
  case vars of
    [] -> Readback.readback env target
    (plicity, var) : vars' -> do
      let env' = Environment.extendVar env var
          domain = lookupVarType var context
      domain' <- Readback.readback env domain
      target' <- varPis context env' vars' target
      let binding = Binding.Unspanned $ lookupVarName var context
      pure $ Syntax.Pi binding domain' plicity target'

lookupMeta
  :: Context v
  -> Meta.Index
  -> M (Meta.Entry M)
lookupMeta context i = do
  m <- readIORef context.metas
  pure $ Meta.lookup i m

lookupEagerMeta
  :: Context v
  -> Meta.Index
  -> M Meta.EagerEntry
lookupEagerMeta context i = do
  m <- readIORef context.metas
  Meta.toEagerEntry $ Meta.lookup i m

solveMeta
  :: Context v
  -> Meta.Index
  -> Syntax.Term Void
  -> M ()
solveMeta context meta term = do
  (arity, unblocked) <- atomicModifyIORef' context.metas $ Meta.solve meta term
  if EnumSet.null unblocked
    then pure ()
    else do
      let emptyContext = emptyFrom context
      value <- Evaluation.evaluate (toEnvironment emptyContext) term
      maybeNewBlockingMeta <- stillBlocked emptyContext arity value
      case maybeNewBlockingMeta of
        Nothing ->
          checkUnblockedPostponedChecks context unblocked
        Just newBlockingMeta ->
          addPostponementsBlockedOnMeta context unblocked newBlockingMeta

lazilySolveMeta
  :: Context v
  -> Meta.Index
  -> Lazy (Syntax.Term Void)
  -> M ()
lazilySolveMeta context meta lazyTerm = do
  (arity, unblocked) <- atomicModifyIORef' context.metas $ Meta.lazilySolve meta $ force lazyTerm
  if EnumSet.null unblocked
    then pure ()
    else do
      let emptyContext =
            emptyFrom context
      term <- force lazyTerm
      value <- Evaluation.evaluate (toEnvironment emptyContext) term
      maybeNewBlockingMeta <- stillBlocked emptyContext arity value
      case maybeNewBlockingMeta of
        Nothing ->
          checkUnblockedPostponedChecks context unblocked
        Just newBlockingMeta ->
          addPostponementsBlockedOnMeta context unblocked newBlockingMeta

metaSolutionMetas :: Context v -> Meta.Index -> M (EnumSet Meta.Index)
metaSolutionMetas context index = do
  m <- readIORef context.metas
  (result, m') <- Meta.solutionMetas index m
  writeIORef context.metas m'
  pure $ foldMap ((.unsolved) <> (.solved)) result

-------------------------------------------------------------------------------

forceNeutral :: Context v -> Domain.Head -> Domain.Spine -> M (Maybe (M Domain.Value))
forceNeutral context head_ spine
  | Domain.Var var <- head_
  , Just value <- EnumMap.lookup var context.values =
      pure $ Just $ Evaluation.applySpine value spine
  | Just spineEqualities <- HashMap.lookup head_ context.equal =
      findSpineEquality spineEqualities
  | otherwise = chooseDefaultBranch
  where
    findSpineEquality [] = chooseDefaultBranch
    findSpineEquality ((eqSpine, eqValue) : rest)
      | Just (spinePrefix, spineSuffix) <- Domain.matchSpinePrefix spine eqSpine = do
          eq <- Unification.equalSpines context spinePrefix eqSpine
          if eq
            then pure $ Just $ Evaluation.applySpine eqValue spineSuffix
            else findSpineEquality rest
      | otherwise = findSpineEquality rest

    chooseDefaultBranch =
      case spine of
        (Domain.Spine _ (_ Seq.:<| _))
          | Just spineInequalities <- HashMap.lookup head_ context.notEqual -> do
              findMatchingDefaultBranch spineInequalities
        _ -> metaSolution

    findMatchingDefaultBranch [] = metaSolution
    findMatchingDefaultBranch ((eqSpine, coveredConstrs, coveredLits) : rest)
      | Just (spinePrefix, Domain.Spine Seq.Empty spineSuffix) <- Domain.matchSpinePrefix spine eqSpine =
          case spineSuffix of
            (Domain.Branches env (Syntax.ConstructorBranches typeName cbrs) (Just defaultBranch), args) Seq.:<| spineSuffix' -> do
              eq <- Unification.equalSpines context spinePrefix eqSpine
              if eq && all (\c -> HashSet.member (Name.QualifiedConstructor typeName c) coveredConstrs) (OrderedHashMap.keys cbrs)
                then pure $ Just do
                  branchValue <- Evaluation.evaluate env defaultBranch
                  Evaluation.applySpine branchValue $ Domain.Spine args spineSuffix'
                else findMatchingDefaultBranch rest
            (Domain.Branches env (Syntax.LiteralBranches lbrs) (Just defaultBranch), args) Seq.:<| spineSuffix' -> do
              eq <- Unification.equalSpines context spinePrefix eqSpine
              if eq && all (`HashSet.member` coveredLits) (OrderedHashMap.keys lbrs)
                then pure $ Just do
                  branchValue <- Evaluation.evaluate env defaultBranch
                  Evaluation.applySpine branchValue $ Domain.Spine args spineSuffix'
                else findMatchingDefaultBranch rest
            _ -> findMatchingDefaultBranch rest
      | otherwise = findMatchingDefaultBranch rest

    metaSolution = case head_ of
      Domain.Meta metaIndex -> do
        meta <- lookupEagerMeta context metaIndex
        case meta of
          Meta.EagerSolved headValue _ _ -> do
            pure $ Just do
              headValue' <- Evaluation.evaluate Environment.empty headValue
              Evaluation.applySpine headValue' spine
          Meta.EagerUnsolved {} ->
            pure Nothing
      _ -> pure Nothing

-- | Evaluate the head of a value further, if (now) possible due to meta
-- solutions or new value bindings. Also evaluates through glued values.
forceHead
  :: Context v
  -> Domain.Value
  -> M Domain.Value
forceHead context value =
  case value of
    Domain.Neutral head_ spine -> do
      maybeEqValue <- forceNeutral context head_ spine
      case maybeEqValue of
        Just meqValue -> do
          value'' <- meqValue
          forceHead context value''
        Nothing ->
          pure value
    Domain.Stuck head_ args value' spine ->
      undefined -- TODO
    Domain.Glued _ _ value' ->
      forceHead context value'
    Domain.Lazy lazyValue -> do
      value' <- force lazyValue
      forceHead context value'
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
    Domain.Neutral head_ spine -> do
      maybeEqValue <- forceNeutral context head_ spine
      case maybeEqValue of
        Just meqValue -> do
          lazyValue <- lazy meqValue
          pure $ Domain.Glued head_ spine $ Domain.Lazy lazyValue
        Nothing ->
          pure value
    Domain.Stuck head_ args value' spine ->
      undefined -- TODO
    Domain.Lazy lazyValue -> do
      value' <- force lazyValue
      forceHeadGlue context value'
    _ ->
      pure value

instantiateType
  :: Context v
  -> Domain.Type
  -> Seq (Plicity, Domain.Value)
  -> M Domain.Type
instantiateType context type_ spine = do
  type' <- forceHead context type_
  case (type', spine) of
    (_, Seq.Empty) ->
      pure type'
    (Domain.Fun _ plicity1 target, (plicity2, _) Seq.:<| spine')
      | plicity1 == plicity2 ->
          instantiateType context target spine'
    (Domain.Pi _ _ plicity1 targetClosure, (plicity2, arg) Seq.:<| spine')
      | plicity1 == plicity2 -> do
          target <- Evaluation.evaluateClosure targetClosure arg
          instantiateType context target spine'
    _ ->
      panic "instantiateType"

-------------------------------------------------------------------------------
-- Error reporting

report :: Context v -> Error.Elaboration -> M ()
report context err =
  let err' =
        Error.Elaboration context.definitionKind context.definitionName $
          Error.Spanned context.span err
   in atomicModifyIORef' context.errors \errs ->
        (errs Tsil.:> err', ())

reportParseError :: Context v -> Error.Parsing -> M ()
reportParseError context err = do
  maybeFilePath <- fetch $ Query.ModuleFile $ moduleName context
  forM_ maybeFilePath \filePath -> do
    let err' =
          Error.Parse filePath err
    atomicModifyIORef' context.errors \errs ->
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
  postponedRef <- newIORef (mempty :: EnumMap Postponement.Index (Maybe (Syntax.Term Void)))
  let zonkMeta index = do
        indexMap <- readIORef metasRef
        case EnumMap.lookup index indexMap of
          Nothing -> do
            meta <- lookupEagerMeta context index
            case meta of
              Meta.EagerUnsolved {} -> do
                atomicModifyIORef' metasRef \indexMap' ->
                  (EnumMap.insert index Nothing indexMap', ())
                pure Nothing
              Meta.EagerSolved term' _ _ -> do
                term'' <- Zonking.zonkTerm Environment.empty zonkMeta zonkPostponed term'
                atomicModifyIORef' metasRef \indexMap' ->
                  (EnumMap.insert index (Just term'') indexMap', ())
                pure $ Just term''
          Just solution ->
            pure solution

      zonkPostponed :: Domain.Environment v -> Postponement.Index -> M (Maybe (Syntax.Term v))
      zonkPostponed env index = do
        indexMap <- readIORef postponedRef
        case EnumMap.lookup index indexMap of
          Nothing -> do
            solution <- lookupPostponedCheck index context
            case solution of
              Postponed.Unchecked {} -> do
                atomicModifyIORef' postponedRef \indexMap' ->
                  (EnumMap.insert index Nothing indexMap', ())
                pure Nothing
              Postponed.Checking -> do
                atomicModifyIORef' postponedRef \indexMap' ->
                  (EnumMap.insert index Nothing indexMap', ())
                pure Nothing
              Postponed.Checked term' -> do
                term'' <- Zonking.zonkTerm env zonkMeta zonkPostponed $ Syntax.coerce term'
                atomicModifyIORef' postponedRef \indexMap' ->
                  (EnumMap.insert index (Just $ Syntax.coerce term'') indexMap', ())
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
  postponementIndex <- atomicModifyIORef' context.postponed $ Postponed.insert check
  addPostponementBlockedOnMeta context postponementIndex blockingMeta
  pure postponementIndex

addPostponementBlockedOnMeta :: Context v -> Postponement.Index -> Meta.Index -> M ()
addPostponementBlockedOnMeta context postponementIndex blockingMeta =
  atomicModifyIORef' context.metas \m -> (Meta.addPostponedIndex blockingMeta postponementIndex m, ())

addPostponementsBlockedOnMeta :: Context v -> EnumSet Postponement.Index -> Meta.Index -> M ()
addPostponementsBlockedOnMeta context postponementIndices blockingMeta =
  atomicModifyIORef' context.metas \m -> (Meta.addPostponedIndices blockingMeta postponementIndices m, ())

lookupPostponedCheck
  :: Postponement.Index
  -> Context v
  -> M Postponed.Check
lookupPostponedCheck i context =
  Postponed.lookup i <$> readIORef context.postponed

checkUnblockedPostponedChecks :: Context v -> EnumSet Postponement.Index -> M ()
checkUnblockedPostponedChecks context indices_ =
  forM_ (EnumSet.toList indices_) \index ->
    join $
      atomicModifyIORef' context.postponed \postponed' -> do
        let (doIt, postponed'') =
              Postponed.adjustF adjust index postponed'

            adjust check =
              case check of
                Postponed.Unchecked check' ->
                  ( do
                      result <- check' Postponement.CanPostpone
                      atomicModifyIORef' context.postponed \p' ->
                        (Postponed.update index (Postponed.Checked result) p', ())
                  , check
                  )
                Postponed.Checking ->
                  (pure (), check)
                Postponed.Checked _ ->
                  (pure (), check)
        (postponed'', doIt)

inferAllPostponedChecks :: Context v -> M ()
inferAllPostponedChecks context =
  go 0
  where
    go index =
      join $
        atomicModifyIORef' context.postponed \postponed' ->
          if index < Postponed.nextIndex postponed'
            then do
              let (doIt, postponed'') =
                    Postponed.adjustF adjust index postponed'

                  adjust value =
                    case value of
                      Postponed.Unchecked check ->
                        ( do
                            result <- check Postponement.Can'tPostpone
                            atomicModifyIORef' context.postponed \p' ->
                              (Postponed.update index (Postponed.Checked result) p', ())
                        , Postponed.Checking
                        )
                      Postponed.Checking ->
                        (pure (), value)
                      Postponed.Checked _ ->
                        (pure (), value)

              (postponed'', do doIt; go $ index + 1)
            else (postponed', pure ())

reportCoverage :: Context v -> M ()
reportCoverage context = do
  coverageChecks <- atomicModifyIORef' context.coverageChecks (mempty,)
  forM_ coverageChecks \coverageCheck -> do
    usedClauses <- readIORef coverageCheck.usedClauses
    forM_ (Set.difference coverageCheck.allClauses usedClauses) \span ->
      report (spanned span context) $ Error.RedundantMatch coverageCheck.matchKind
