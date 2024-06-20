{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoFieldSelectors #-}

module ReferenceCounting where

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import Index (Index)
import qualified Index.Map
import qualified Index.Map as Index (Map)
import Literal (Literal)
import Low.PassBy (PassBy)
import qualified Low.PassBy as PassBy
import Low.Representation (Representation)
import qualified Low.Representation as Representation
import qualified Low.Syntax as Syntax
import Monad hiding (State)
import Name (Name)
import qualified Name
import Protolude hiding (evaluate, repr)
import Var (Var)

data Killed = NotKilled | Killed
  deriving (Show)

data Dead = NotDead | Dead
  deriving (Show)

data Value
  = Operand !Operand
  | Let !PassBy !Name !Var !Dead !Value !Value
  | Seq !Value !Value
  | Case !Operand [(EnumSet Var, Branch)] (Maybe (EnumSet Var, Value))
  | Call !Name.Lowered [Operand]
  | StackAllocate !Operand
  | HeapAllocate !Name.QualifiedConstructor !Operand
  | HeapPayload !Operand
  | PointerTag !Operand
  | Offset !Operand !Operand
  | Copy !Operand !Operand !Operand
  | Store !Operand !Operand !Representation
  | Load !Operand !Representation
  | IncreaseReferenceCount !Operand !Representation
  | DecreaseReferenceCount !Operand !Representation
  deriving (Show)

data Operand
  = Var !Killed !Var
  | Global !Representation !Name.Lowered
  | Literal !Literal
  | Representation !Representation
  | Tag !Name.QualifiedConstructor
  | Undefined !Representation
  deriving (Show)

data Branch
  = ConstructorBranch !Name.QualifiedConstructor !Value
  | LiteralBranch !Literal !Value
  deriving (Show)

referenceCountDefinition :: Syntax.Definition -> M Syntax.Definition
referenceCountDefinition = \case
  def@(Syntax.ConstantDefinition _) -> pure def
  Syntax.FunctionDefinition function ->
    Syntax.FunctionDefinition <$> referenceCountFunction Index.Map.Empty mempty function

referenceCountFunction :: Index.Map v Var -> EnumSet Var -> Syntax.Function v -> M (Syntax.Function v)
referenceCountFunction env liveOut = \case
  Syntax.Body passBy term -> do
    (value, liveIn) <- evaluate env liveOut term
    when (liveIn /= liveOut) $ panic "liveIn liveOut mismatch"
    value' <-
      flip
        evalStateT
        ReferenceCountState
          { provenances = mempty
          , children = mempty
          }
        $ do
          (value', valueProvenance) <- referenceCount passBy value
          case valueProvenance of
            Nothing -> case passBy of
              PassBy.Reference -> pure value'
              PassBy.Value repr -> increase value' repr
            Just (Owned _) -> pure value'
            Just (Child _) -> panic "Returning child"
    pure $ Syntax.Body passBy $ readback env value'
  Syntax.Parameter name passBy function -> do
    var <- freshVar
    function' <- referenceCountFunction (env Index.Map.:> var) (EnumSet.insert var liveOut) function
    pure $ Syntax.Parameter name passBy function'

evaluate :: Index.Map v Var -> EnumSet Var -> Syntax.Term v -> M (Value, EnumSet Var)
evaluate env liveOut = \case
  Syntax.Operand operand -> do
    let (operand', liveIn) = evaluateOperand env liveOut operand
    pure (Operand operand', liveIn)
  Syntax.Let passBy name term body -> do
    var <- freshVar
    (body', bodyLiveIn) <- evaluate (env Index.Map.:> var) liveOut body
    (term', liveIn) <- evaluate env bodyLiveIn term
    pure
      ( Let passBy name var (if EnumSet.member var bodyLiveIn then NotDead else Dead) term' body'
      , EnumSet.delete var liveIn
      )
  Syntax.Seq lhs rhs -> do
    (rhs', rhsLiveIn) <- evaluate env liveOut rhs
    (lhs', liveIn) <- evaluate env rhsLiveIn lhs
    pure (Seq lhs' rhs', liveIn)
  Syntax.Case scrutinee branches maybeDefaultBranch -> do
    branches' <- mapM (evaluateBranch env liveOut) branches
    maybeDefaultBranch' <- mapM (evaluate env liveOut) maybeDefaultBranch
    let branchesLiveIn = foldMap snd branches' <> foldMap snd maybeDefaultBranch'
    let (scrutinee', liveIn) = evaluateOperand env branchesLiveIn scrutinee
    pure
      ( Case
          scrutinee'
          ( (\(branch, branchLiveIn) -> (branchesLiveIn EnumSet.\\ branchLiveIn, branch))
              <$> branches'
          )
          ( (\(branch, branchLiveIn) -> (branchesLiveIn EnumSet.\\ branchLiveIn, branch))
              <$> maybeDefaultBranch'
          )
      , liveIn
      )
  Syntax.Call global args -> do
    let (args', liveIn) = foldr (\operand (as, liveOut') -> first (: as) $ evaluateOperand env liveOut' operand) (mempty, liveOut) args
    pure (Call global args', liveIn)
  Syntax.StackAllocate size -> do
    let (size', liveIn) = evaluateOperand env liveOut size
    pure (StackAllocate size', liveIn)
  Syntax.HeapAllocate constr size -> do
    let (size', liveIn) = evaluateOperand env liveOut size
    pure (HeapAllocate constr size', liveIn)
  Syntax.HeapPayload pointer -> do
    let (pointer', liveIn) = evaluateOperand env liveOut pointer
    pure (HeapPayload pointer', liveIn)
  Syntax.PointerTag pointer -> do
    let (pointer', liveIn) = evaluateOperand env liveOut pointer
    pure (PointerTag pointer', liveIn)
  Syntax.Offset ref size -> do
    let (size', sizeLiveIn) = evaluateOperand env liveOut size
    let (ref', liveIn) = evaluateOperand env sizeLiveIn ref
    pure (Offset ref' size', liveIn)
  Syntax.Copy dst src size -> do
    let (size', sizeLiveIn) = evaluateOperand env liveOut size
    let (src', srcLiveIn) = evaluateOperand env sizeLiveIn src
    let (dst', liveIn) = evaluateOperand env srcLiveIn dst
    pure (Copy dst' src' size', liveIn)
  Syntax.Store dst src repr -> do
    let (src', srcLiveIn) = evaluateOperand env liveOut src
    let (dst', liveIn) = evaluateOperand env srcLiveIn dst
    pure (Store dst' src' repr, liveIn)
  Syntax.Load ref repr -> do
    let (ref', liveIn) = evaluateOperand env liveOut ref
    pure (Load ref' repr, liveIn)
  Syntax.IncreaseReferenceCount {} -> panic "RC operations before reference counting"
  Syntax.DecreaseReferenceCount {} -> panic "RC operations before reference counting"

evaluateOperand :: Index.Map v Var -> EnumSet Var -> Syntax.Operand v -> (Operand, EnumSet Var)
evaluateOperand env liveOut = \case
  Syntax.Var index -> do
    let var = Index.Map.index env index
    (Var (if EnumSet.member var liveOut then NotKilled else Killed) var, EnumSet.insert var liveOut)
  Syntax.Global repr global -> (Global repr global, liveOut)
  Syntax.Literal lit -> (Literal lit, liveOut)
  Syntax.Representation repr -> (Representation repr, liveOut)
  Syntax.Tag constr -> (Tag constr, liveOut)
  Syntax.Undefined repr -> (Undefined repr, liveOut)

evaluateBranch :: Index.Map v Var -> EnumSet Var -> Syntax.Branch v -> M (Branch, EnumSet Var)
evaluateBranch env liveOut = \case
  Syntax.LiteralBranch lit branch -> do
    (branch', liveIn) <- evaluate env liveOut branch
    pure (LiteralBranch lit branch', liveIn)
  Syntax.ConstructorBranch constr branch -> do
    (branch', liveIn) <- evaluate env liveOut branch
    pure (ConstructorBranch constr branch', liveIn)

data ReferenceCountState = ReferenceCountState
  { provenances :: EnumMap Var Provenance
  , children :: EnumMap Var Int
  }
  deriving (Show)

type ReferenceCount = StateT ReferenceCountState M

data Provenance
  = Owned !Representation
  | Child !Var
  deriving (Show)

referenceCount :: PassBy -> Value -> ReferenceCount (Value, Maybe Provenance)
referenceCount passBy value = case value of
  Operand operand -> case operand of
    Var Killed var -> do
      provenances <- gets (.provenances)
      pure (value, EnumMap.lookup var provenances)
    Var NotKilled _ -> do
      maybeParent <- tryMakeParent operand
      pure (value, Child <$> maybeParent)
    Global _ _ -> pure (value, Nothing)
    Literal _ -> pure (value, Nothing)
    Representation _ -> pure (value, Nothing)
    Tag _ -> pure (value, Nothing)
    Undefined _ -> pure (value, Nothing)
  Let passValBy name var dead val body -> do
    (val', maybeValProvenance) <- referenceCount passValBy val
    forM_ maybeValProvenance \valProvenance ->
      modify \s -> s {provenances = EnumMap.insert var valProvenance s.provenances}
    val'' <- case dead of
      NotDead ->
        pure val'
      Dead -> do
        decrease <- referenceCountOperand $ Var Killed var
        decreaseAfter decrease val' passValBy
    (body', bodyProvenance) <- referenceCount passBy body
    pure (Let passValBy name var dead val'' body', bodyProvenance)
  Seq lhs rhs -> do
    (lhs', lhsProvenance) <- referenceCount (PassBy.Value mempty) lhs
    when (isJust lhsProvenance) $ panic $ "Seq with provenance " <> show lhs'
    (rhs', rhsProvenance) <- referenceCount passBy rhs
    pure (Seq lhs' rhs', rhsProvenance)
  Case scrutinee branches maybeDefaultBranch -> do
    decreaseScrutinee <- referenceCountOperand scrutinee
    startingState <- get
    branches' <- forM branches \(killedVars, branch) -> do
      put startingState
      decreases <- catMaybes <$> forM (EnumSet.toList killedVars) kill
      branch' <- case branch of
        ConstructorBranch constr branchValue -> do
          (branchValue', provenance) <- referenceCount passBy branchValue
          when (isJust provenance) $ panic $ "Branch with provenance " <> show branchValue'
          pure $ ConstructorBranch constr $ decreaseBefore decreases branchValue'
        LiteralBranch lit branchValue -> do
          (branchValue', provenance) <- referenceCount passBy branchValue
          when (isJust provenance) $ panic $ "Branch with provenance " <> show branchValue'
          pure $ LiteralBranch lit $ decreaseBefore decreases branchValue'
      pure (killedVars, branch')
    maybeDefaultBranch' <- forM maybeDefaultBranch \(killedVars, branch) -> do
      put startingState
      decreases <- catMaybes <$> forM (EnumSet.toList killedVars) kill
      (branch', provenance) <- referenceCount passBy branch
      when (isJust provenance) $ panic $ "Branch with provenance " <> show branch'
      pure (killedVars, decreaseBefore decreases branch')
    value' <- decreaseAfter decreaseScrutinee (Case scrutinee branches' maybeDefaultBranch') passBy
    pure (value', Nothing)
  Call _ args -> do
    decreases <- catMaybes <$> mapM referenceCountOperand args
    value' <- decreaseAfter decreases value passBy
    pure
      ( value'
      , case passBy of
          PassBy.Value repr
            | needsReferenceCounting repr -> Just $ Owned repr
            | otherwise -> Nothing
          PassBy.Reference -> Nothing
      )
  StackAllocate _ ->
    pure (value, Nothing)
  HeapAllocate _ _ ->
    pure (value, Just $ Owned Representation.pointer)
  HeapPayload pointer -> do
    maybeParent <- tryMakeParent pointer
    pure (value, Child <$> maybeParent)
  PointerTag operand -> do
    decrease <- referenceCountOperand operand
    value' <- decreaseAfter decrease value passBy
    pure (value', Nothing)
  Offset base _ -> do
    maybeParent <- tryMakeParent base
    pure (value, Child <$> maybeParent)
  Copy dst src _ -> do
    decreaseDst <- referenceCountOperand dst
    decreaseSrc <- referenceCountOperand src
    value' <- decreaseAfter decreaseDst value passBy
    value'' <- decreaseAfter decreaseSrc value' passBy
    pure (value'', Nothing)
  Store dst (Var Killed src) _ -> do
    decreaseDst <- referenceCountOperand dst
    decreaseSrc <- kill src
    value' <- decreaseAfter decreaseDst value passBy
    case decreaseSrc of
      Just (var, _) | var == src -> do
        pure (value', Nothing)
      _ -> do
        value'' <- decreaseAfter decreaseSrc value' passBy
        pure (value'', Nothing)
  Store dst src repr -> do
    decreaseDst <- referenceCountOperand dst
    decreaseSrc <- referenceCountOperand src
    let value' = increaseBefore src repr value
    value'' <- decreaseAfter decreaseDst value' passBy
    value''' <- decreaseAfter decreaseSrc value'' passBy
    pure (value''', Nothing)
  Load src repr
    | needsReferenceCounting repr -> do
        maybeParent <- tryMakeParent src
        case maybeParent of
          Nothing -> do
            decrease <- referenceCountOperand src
            value' <- decreaseAfter decrease value passBy
            pure (value', Nothing)
          Just parent -> do
            pure (value, Just $ Child parent)
    | otherwise -> do
        decreaseSrc <- referenceCountOperand src
        value' <- decreaseAfter decreaseSrc value passBy
        pure (value', Nothing)
  IncreaseReferenceCount {} -> panic "RC operations before reference counting"
  DecreaseReferenceCount {} -> panic "RC operations before reference counting"

needsReferenceCounting :: Representation -> Bool
needsReferenceCounting repr = repr.pointers > 0

increaseBefore :: Operand -> Representation -> Value -> Value
increaseBefore operand repr value
  | needsReferenceCounting repr = Seq (IncreaseReferenceCount operand repr) value
  | otherwise = value

increase :: Value -> Representation -> ReferenceCount Value
increase value repr
  | needsReferenceCounting repr = do
      var <- lift freshVar
      pure $
        Let (PassBy.Value repr) "temp" var NotDead value $
          Seq (IncreaseReferenceCount (Var Killed var) repr) $
            Operand $
              Var Killed var
  | otherwise = pure value

decreaseBefore
  :: Foldable f
  => f (Var, Representation)
  -> Value
  -> Value
decreaseBefore vars value =
  foldr
    ( \(v, repr) ->
        if needsReferenceCounting repr
          then Seq $ DecreaseReferenceCount (Var Killed v) repr
          else identity
    )
    value
    vars

decreaseAfter
  :: Foldable f
  => f (Var, Representation)
  -> Value
  -> PassBy
  -> ReferenceCount Value
decreaseAfter vars value passBy =
  case vars' of
    [] -> pure value
    _ -> do
      var <- lift freshVar
      pure $
        Let passBy "temp" var NotDead value $
          decreaseBefore vars' $
            Operand $
              Var Killed var
  where
    vars' = filter (needsReferenceCounting . snd) $ toList vars

tryMakeParent :: Operand -> ReferenceCount (Maybe Var)
tryMakeParent = \case
  Var _ var -> do
    provenances <- gets (.provenances)
    case EnumMap.lookup var provenances of
      Just (Owned _) -> do
        modify \s -> s {children = EnumMap.insertWith (\_ old -> old + 1) var 1 s.children}
        pure $ Just var
      Just (Child parent) -> do
        modify \s -> s {children = EnumMap.insertWith (\_ old -> old + 1) parent 1 s.children}
        pure $ Just parent
      _ -> pure Nothing
  Global _ _ -> pure Nothing
  Literal _ -> pure Nothing
  Representation _ -> pure Nothing
  Tag _ -> pure Nothing
  Undefined _ -> pure Nothing

referenceCountOperand :: Operand -> ReferenceCount (Maybe (Var, Representation))
referenceCountOperand = \case
  Var Killed var -> kill var
  Var NotKilled _ -> pure Nothing
  Global _ _ -> pure Nothing
  Literal _ -> pure Nothing
  Representation _ -> pure Nothing
  Tag _ -> pure Nothing
  Undefined _ -> pure Nothing

kill :: Var -> ReferenceCount (Maybe (Var, Representation))
kill var = do
  provenances <- gets (.provenances)
  case EnumMap.lookup var provenances of
    Nothing -> pure Nothing
    Just (Owned repr) -> do
      modify \s -> s {children = EnumMap.insertWith (\_ old -> old - 1) var 0 s.children}
      children <- gets (.children)
      case EnumMap.findWithDefault (panic "no entry") var children of
        0 -> do
          modify \s ->
            s
              { provenances = EnumMap.delete var s.provenances
              , children = EnumMap.delete var s.children
              }
          pure $ Just (var, repr)
        _ -> pure Nothing
    Just (Child parent) -> do
      modify \s -> s {children = EnumMap.adjust (subtract 1) parent s.children}
      children <- gets (.children)
      case (EnumMap.findWithDefault (panic "no entry") parent children, EnumMap.findWithDefault (panic "no entry") parent provenances) of
        (0, Owned repr) -> do
          modify \s ->
            s
              { provenances = EnumMap.delete parent s.provenances
              , children = EnumMap.delete parent s.children
              }
          pure $ Just (parent, repr)
        (0, _) -> panic "Non-owned variable with children"
        _ -> pure Nothing

-------------------------------------------------------------------------------

readback :: Index.Map v Var -> Value -> Syntax.Term v
readback env = \case
  Operand operand -> Syntax.Operand $ readbackOperand env operand
  Let passBy name var _dead value value' ->
    Syntax.Let
      passBy
      name
      (readback env value)
      (readback (env Index.Map.:> var) value')
  Seq value value' ->
    Syntax.Seq (readback env value) (readback env value')
  Case scrutinee branches maybeDefaultBranch ->
    Syntax.Case
      (readbackOperand env scrutinee)
      (readbackBranch env . snd <$> branches)
      (readback env . snd <$> maybeDefaultBranch)
  Call fun args -> Syntax.Call fun $ readbackOperand env <$> args
  StackAllocate repr -> Syntax.StackAllocate $ readbackOperand env repr
  HeapAllocate con repr -> Syntax.HeapAllocate con $ readbackOperand env repr
  HeapPayload operand -> Syntax.HeapPayload $ readbackOperand env operand
  PointerTag operand -> Syntax.PointerTag $ readbackOperand env operand
  Offset base offset ->
    Syntax.Offset
      (readbackOperand env base)
      (readbackOperand env offset)
  Copy dst src size ->
    Syntax.Copy
      (readbackOperand env dst)
      (readbackOperand env src)
      (readbackOperand env size)
  Store dst value repr -> Syntax.Store (readbackOperand env dst) (readbackOperand env value) repr
  Load src repr -> Syntax.Load (readbackOperand env src) repr
  IncreaseReferenceCount operand repr -> Syntax.IncreaseReferenceCount (readbackOperand env operand) repr
  DecreaseReferenceCount operand repr -> Syntax.DecreaseReferenceCount (readbackOperand env operand) repr

readbackOperand :: Index.Map v Var -> Operand -> Syntax.Operand v
readbackOperand env = \case
  Var _ var -> Syntax.Var $ readbackVar env var
  Global repr global -> Syntax.Global repr global
  Literal lit -> Syntax.Literal lit
  Representation repr -> Syntax.Representation repr
  Tag tag -> Syntax.Tag tag
  Undefined repr -> Syntax.Undefined repr

readbackVar :: Index.Map v Var -> Var -> Index v
readbackVar env var =
  fromMaybe (panic "Lower.readbackVar") $
    Index.Map.elemIndex var env

readbackBranch :: Index.Map v Var -> Branch -> Syntax.Branch v
readbackBranch env = \case
  ConstructorBranch con value -> Syntax.ConstructorBranch con $ readback env value
  LiteralBranch lit value -> Syntax.LiteralBranch lit $ readback env value
