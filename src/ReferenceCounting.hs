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
  | Let !PassBy !Name !Var !Dead !LetOperation !Value
  | Seq !SeqOperation !Value
  deriving (Show)

data LetOperation
  = Case !Operand [(EnumSet Var, Branch)] (Maybe (EnumSet Var, Value))
  | Call !Name.Lowered [Operand]
  | StackAllocate !Operand
  | HeapAllocate !Name.QualifiedConstructor !Operand
  | HeapPayload !Operand
  | PointerTag !Operand
  | Offset !Operand !Operand
  | Load !Operand !Representation
  deriving (Show)

data SeqOperation
  = Store !Operand !Operand !Representation
  | Copy !Operand !Operand !Operand
  | IncreaseReferenceCount !Operand !Representation
  | IncreaseReferenceCounts !Operand !Operand
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
          }
        $ referenceCount passBy value
    pure $ Syntax.Body passBy $ readback env value'
  Syntax.Parameter name passBy function -> do
    var <- freshVar
    function' <- referenceCountFunction (env Index.Map.:> var) (EnumSet.insert var liveOut) function
    pure $ Syntax.Parameter name passBy function'

evaluate
  :: Index.Map v Var
  -> EnumSet Var
  -> Syntax.Term v
  -> M (Value, EnumSet Var)
evaluate env liveOut = \case
  Syntax.Operand operand -> do
    let (operand', liveIn) = evaluateOperand env liveOut operand
    pure (Operand operand', liveIn)
  Syntax.Let passBy name operation body -> do
    var <- freshVar
    (body', bodyLiveIn) <- evaluate (env Index.Map.:> var) liveOut body
    (operation', liveIn) <- evaluateLetOperation env bodyLiveIn operation
    pure
      ( Let passBy name var (if EnumSet.member var bodyLiveIn then NotDead else Dead) operation' body'
      , EnumSet.delete var liveIn
      )
  Syntax.Seq lhs rhs -> do
    (rhs', rhsLiveIn) <- evaluate env liveOut rhs
    (lhs', liveIn) <- evaluateSeqOperation env rhsLiveIn lhs
    pure (Seq lhs' rhs', liveIn)

evaluateLetOperation
  :: Index.Map v Var
  -> EnumSet Var
  -> Syntax.LetOperation v
  -> M (LetOperation, EnumSet Var)
evaluateLetOperation env liveOut = \case
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
  Syntax.Load ref repr -> do
    let (ref', liveIn) = evaluateOperand env liveOut ref
    pure (Load ref' repr, liveIn)

evaluateSeqOperation
  :: Index.Map v Var
  -> EnumSet Var
  -> Syntax.SeqOperation v
  -> M (SeqOperation, EnumSet Var)
evaluateSeqOperation env liveOut = \case
  Syntax.Copy dst src size -> do
    let (size', sizeLiveIn) = evaluateOperand env liveOut size
    let (src', srcLiveIn) = evaluateOperand env sizeLiveIn src
    let (dst', liveIn) = evaluateOperand env srcLiveIn dst
    pure (Copy dst' src' size', liveIn)
  Syntax.Store dst src repr -> do
    let (src', srcLiveIn) = evaluateOperand env liveOut src
    let (dst', liveIn) = evaluateOperand env srcLiveIn dst
    pure (Store dst' src' repr, liveIn)
  Syntax.IncreaseReferenceCount {} -> panic "RC operations before reference counting"
  Syntax.IncreaseReferenceCounts {} -> panic "RC operations before reference counting"
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
  }
  deriving (Show)

type ReferenceCount = StateT ReferenceCountState M

data Provenance
  = Owned !PassBy !Int
  | Child !Var
  deriving (Show)

referenceCount :: PassBy -> Value -> ReferenceCount Value
referenceCount passBy value = case value of
  Operand operand -> do
    decrease <- referenceCountOperand operand
    pure
      if cancelOut operand decrease
        then value
        else case passBy of
          PassBy.Reference -> decreases decrease value
          PassBy.Value repr -> increase operand repr $ decreases decrease value
  Let passValBy name var dead operation body -> do
    (operation', maybeOperationProvenance, decreaseAfters) <- referenceCountLetOperation passValBy operation
    forM_ maybeOperationProvenance \valProvenance ->
      modify \s -> s {provenances = EnumMap.insert var valProvenance s.provenances}
    decreaseVar <- case dead of
      NotDead -> pure Nothing
      Dead -> referenceCountOperand $ Var Killed var
    body' <- referenceCount passBy body
    modify \s -> s {provenances = EnumMap.delete var s.provenances}
    pure $ Let passValBy name var dead operation' $ decreases decreaseAfters $ decreases decreaseVar body'
  Seq lhs rhs -> do
    (increaseBefores, increaseRefsBefore, decreaseAfters) <- referenceCountSeqOperation lhs
    rhs' <- referenceCount passBy rhs
    pure $ increaseRefs increaseRefsBefore $ increases increaseBefores $ Seq lhs $ decreases decreaseAfters rhs'

referenceCountLetOperation
  :: PassBy
  -> LetOperation
  -> ReferenceCount (LetOperation, Maybe Provenance, [(Var, Representation)])
referenceCountLetOperation passBy operation = case operation of
  Case scrutinee branches maybeDefaultBranch -> do
    decreaseScrutinee <- referenceCountOperand scrutinee
    startingState <- get
    branches' <- forM branches \(killedVars, branch) -> do
      put startingState
      kills <- catMaybes <$> forM (EnumSet.toList killedVars) kill
      branch' <- case branch of
        ConstructorBranch constr branchValue -> do
          branchValue' <- referenceCount passBy branchValue
          pure $ ConstructorBranch constr $ decreases kills branchValue'
        LiteralBranch lit branchValue -> do
          branchValue' <- referenceCount passBy branchValue
          pure $ LiteralBranch lit $ decreases kills branchValue'
      pure (killedVars, branch')
    maybeDefaultBranch' <- forM maybeDefaultBranch \(killedVars, branch) -> do
      put startingState
      kills <- catMaybes <$> forM (EnumSet.toList killedVars) kill
      branch' <- referenceCount passBy branch
      pure (killedVars, decreases kills branch')
    pure (Case scrutinee branches' maybeDefaultBranch', Nothing, maybeToList decreaseScrutinee)
  Call _ args -> do
    decreaseArgs <- catMaybes <$> mapM referenceCountOperand args
    pure
      ( operation
      , case passBy of
          PassBy.Value repr
            | needsReferenceCounting repr -> Just $ Owned (PassBy.Value repr) 1
            | otherwise -> Nothing
          PassBy.Reference -> Nothing
      , decreaseArgs
      )
  StackAllocate _ ->
    pure (operation, Just $ Owned PassBy.Reference 1, [])
  HeapAllocate _ _ ->
    pure (operation, Just $ Owned (PassBy.Value Representation.pointer) 1, [])
  HeapPayload pointer -> do
    decrease <- referenceCountOperand pointer
    maybeParent <- tryMakeParent pointer
    pure (operation, Child <$> maybeParent, maybeToList decrease)
  PointerTag operand -> do
    decrease <- referenceCountOperand operand
    pure (operation, Nothing, maybeToList decrease)
  Offset base _ -> do
    maybeParent <- tryMakeParent base
    pure (operation, Child <$> maybeParent, [])
  Load src repr -> do
    maybeParent <-
      if needsReferenceCounting repr
        then tryMakeParent src
        else pure Nothing
    decreaseSrc <- referenceCountOperand src
    pure (operation, Child <$> maybeParent, maybeToList decreaseSrc)

referenceCountSeqOperation
  :: SeqOperation
  -> ReferenceCount (Maybe (Operand, Representation), Maybe (Operand, Operand), [(Var, Representation)])
referenceCountSeqOperation operation = case operation of
  Copy dst src repr -> do
    decreaseDst <- referenceCountOperand dst
    decreaseSrc <- referenceCountOperand src
    pure
      if cancelOut src decreaseSrc
        then (Nothing, Nothing, maybeToList decreaseDst)
        else (Nothing, Just (src, repr), catMaybes [decreaseDst, decreaseSrc])
  Store dst src repr -> do
    decreaseDst <- referenceCountOperand dst
    decreaseSrc <- referenceCountOperand src
    pure
      if cancelOut src decreaseSrc
        then (Nothing, Nothing, maybeToList decreaseDst)
        else (Just (src, repr), Nothing, catMaybes [decreaseDst, decreaseSrc])
  IncreaseReferenceCount {} -> panic "RC operations before reference counting"
  IncreaseReferenceCounts {} -> panic "RC operations before reference counting"
  DecreaseReferenceCount {} -> panic "RC operations before reference counting"

needsReferenceCounting :: Representation -> Bool
needsReferenceCounting repr = repr.pointers > 0

representationOperandNeedsReferenceCounting :: Operand -> Bool
representationOperandNeedsReferenceCounting (Representation repr) = needsReferenceCounting repr
representationOperandNeedsReferenceCounting _ = True

increase :: Operand -> Representation -> Value -> Value
increase operand repr value
  | needsReferenceCounting repr = Seq (IncreaseReferenceCount operand repr) value
  | otherwise = value

increases :: Foldable f => f (Operand, Representation) -> Value -> Value
increases operands value =
  foldr
    ( \(o, repr) ->
        if needsReferenceCounting repr
          then Seq $ IncreaseReferenceCount o repr
          else identity
    )
    value
    operands

increaseRefs :: Foldable f => f (Operand, Operand) -> Value -> Value
increaseRefs operands value =
  foldr
    ( \(o, repr) ->
        if representationOperandNeedsReferenceCounting repr
          then Seq $ IncreaseReferenceCounts o repr
          else identity
    )
    value
    operands

decreases
  :: (Foldable f)
  => f (Var, Representation)
  -> Value
  -> Value
decreases vars value =
  foldr
    ( \(v, repr) ->
        if needsReferenceCounting repr
          then Seq $ DecreaseReferenceCount (Var Killed v) repr
          else identity
    )
    value
    vars

cancelOut :: Operand -> Maybe (Var, Representation) -> Bool
cancelOut (Var _ var) (Just (var', _)) = var == var'
cancelOut _ _ = False

tryMakeParent :: Operand -> ReferenceCount (Maybe Var)
tryMakeParent = \case
  Var _ var -> do
    provenances <- gets (.provenances)
    case EnumMap.lookup var provenances of
      Just (Owned repr rc) -> do
        modify \s -> s {provenances = EnumMap.insert var (Owned repr $ rc + 1) s.provenances}
        pure $ Just var
      Just (Child parent) -> do
        modify \s ->
          s
            { provenances =
                EnumMap.alter
                  ( \case
                      Nothing -> panic "Child without live parent"
                      Just (Owned repr rc) -> Just $ Owned repr $ rc + 1
                      Just (Child _) -> panic "Child without owned parent"
                  )
                  parent
                  s.provenances
            }
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
    Just (Owned passBy 1) -> do
      modify \s -> s {provenances = EnumMap.delete var s.provenances}
      pure case passBy of
        PassBy.Value repr -> Just (var, repr)
        PassBy.Reference -> Nothing
    Just (Owned passBy rc) -> do
      modify \s -> s {provenances = EnumMap.insert var (Owned passBy $ rc - 1) s.provenances}
      pure Nothing
    Just (Child parent) -> do
      case EnumMap.findWithDefault (panic "no entry") parent provenances of
        Owned passBy 1 -> do
          modify \s -> s {provenances = EnumMap.delete var s.provenances}
          pure case passBy of
            PassBy.Value repr -> Just (parent, repr)
            PassBy.Reference -> Nothing
        Owned repr rc -> do
          modify \s -> s {provenances = EnumMap.insert parent (Owned repr $ rc - 1) s.provenances}
          pure Nothing
        Child _ -> panic "non-owned parent"

-------------------------------------------------------------------------------

readback :: Index.Map v Var -> Value -> Syntax.Term v
readback env = \case
  Operand operand -> Syntax.Operand $ readbackOperand env operand
  Let passBy name var _dead operation value' ->
    Syntax.Let
      passBy
      name
      (readbackLetOperation env operation)
      (readback (env Index.Map.:> var) value')
  Seq operation value' ->
    Syntax.Seq (readbackSeqOperation env operation) (readback env value')

readbackLetOperation :: Index.Map v Var -> LetOperation -> Syntax.LetOperation v
readbackLetOperation env = \case
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
  Load src repr -> Syntax.Load (readbackOperand env src) repr

readbackSeqOperation :: Index.Map v Var -> SeqOperation -> Syntax.SeqOperation v
readbackSeqOperation env = \case
  Copy dst src size ->
    Syntax.Copy
      (readbackOperand env dst)
      (readbackOperand env src)
      (readbackOperand env size)
  Store dst value repr -> Syntax.Store (readbackOperand env dst) (readbackOperand env value) repr
  IncreaseReferenceCount operand repr -> Syntax.IncreaseReferenceCount (readbackOperand env operand) repr
  IncreaseReferenceCounts operand repr -> Syntax.IncreaseReferenceCounts (readbackOperand env operand) (readbackOperand env repr)
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
