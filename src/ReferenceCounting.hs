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

type ReferenceCount = State ReferenceCountState

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
    undefined dead
    forM_ maybeValProvenance \valProvenance ->
      modify \s -> s {provenances = EnumMap.insert var valProvenance s.provenances}
    (body', bodyProvenance) <- referenceCount passBy body
    pure (Let passValBy name var dead val' body', bodyProvenance)
  Seq lhs rhs -> do
    (lhs', _lhsProvenance) <- referenceCount (PassBy.Value mempty) lhs
    (rhs', rhsProvenance) <- referenceCount passBy rhs
    pure (Seq lhs' rhs', rhsProvenance)
  Case scrutinee branches maybeDefaultBranch -> undefined
  Call _ args -> do
    decreases <- catMaybes <$> mapM (referenceCountOperand kill) args
    value' <- decreaseAfter decreases value
    pure
      ( value'
      , case passBy of
          PassBy.Value repr -> Just $ Owned repr
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
    decrease <- referenceCountOperand kill operand
    value' <- decreaseAfter decrease value
    pure (value', Nothing)
  Offset base _ -> do
    maybeParent <- tryMakeParent base
    pure (value, Child <$> maybeParent)
  Copy dst src _ -> do
    decreaseDst <- referenceCountOperand kill dst
    decreaseSrc <- referenceCountOperand kill src
    value' <- decreaseAfter decreaseDst value
    value'' <- decreaseAfter decreaseSrc value'
    pure (value'', Nothing)
  Store dst (Var Killed src) _ -> do
    decreaseDst <- referenceCountOperand kill dst
    decreaseSrc <- kill src
    value' <- decreaseAfter decreaseDst value
    case decreaseSrc of
      Just (var, _) | var == src -> do
        pure (value', Nothing)
      _ -> do
        value'' <- decreaseAfter decreaseSrc value'
        pure (value'', Nothing)
  Store dst src repr -> do
    decreaseDst <- referenceCountOperand kill dst
    decreaseSrc <- referenceCountOperand kill src
    value' <- increaseBefore src repr value
    value'' <- decreaseAfter decreaseDst value'
    value''' <- decreaseAfter decreaseSrc value''
    pure (value''', Nothing)
  Load src repr -> do
    maybeParent <- tryMakeParent src
    case maybeParent of
      Nothing -> do
        decrease <- referenceCountOperand kill src
        value' <- increase value repr
        value'' <- decreaseAfter decrease value'
        pure (value'', Just $ Owned repr)
      Just parent -> do
        pure (value, Just $ Child parent)

increaseBefore :: Operand -> Representation -> Value -> ReferenceCount Value
increaseBefore = undefined

increase :: Value -> Representation -> ReferenceCount Value
increase = undefined

decreaseAfter :: f (Var, Representation) -> Value -> ReferenceCount Value
decreaseAfter = undefined

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

referenceCountOperand :: (Var -> ReferenceCount (Maybe a)) -> Operand -> ReferenceCount (Maybe a)
referenceCountOperand onKilled = \case
  Var Killed var -> onKilled var
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

-- data Ownership
--   = Borrowed
--   | Owned
--   deriving (Show)

-- data ReferenceCountState = ReferenceCountState
--   { owned :: EnumMap Var Representation
--   , borrowed :: EnumMap Var Representation
--   }

-- type ReferenceCount = State ReferenceCountState

-- data Provenance
--   = Unmanaged
--   | Managed !Ownership !Representation

-- referenceCount :: Value -> ReferenceCount (Value, Provenance)
-- referenceCount value = case value.payload of
--   Operand operand -> case operand of
--     Var var -> do
--       rc <- get
--       case (EnumMap.lookup var rc.owned, EnumMap.lookup var rc.borrowed) of
--         (Nothing, Nothing) -> pure (value, Unmanaged)
--         (Just repr, _) -> pure (value, Managed Owned repr)
--         (_, Just repr) -> pure (value, Managed Borrowed repr)
--     Global _ _ -> pure (value, Unmanaged)
--     Literal _ -> pure (value, Unmanaged)
--     Representation _ -> pure (value, Unmanaged)
--     Tag _ -> pure (value, Unmanaged)
--     Undefined _ -> pure (value, Unmanaged)
--   Let passBy name var val body -> do
--     do
--       rc <- get
--       let keepAlives = EnumMap.fromSet (const ()) body.keepAlives
--       let valBorrowed = EnumMap.intersection rc.owned keepAlives <> rc.borrowed
--       let valOwned = rc.owned EnumMap.\\ keepAlives
--       put rc {borrowed = valBorrowed, owned = valOwned}
--     (val', provenance) <- referenceCount val

--     case provenance of
--       Unmanaged -> undefined
--       Managed Borrowed repr -> undefined
--       Managed Owned repr -> undefined
--   Seq lhs rhs -> do
--     owned <- gets (.owned)
--     -- EnumMap.intersection rhs.keepAlives
--     undefined
--   Case scrutinee branches maybeDefaultBranch -> undefined
--   Call fun args -> undefined
--   StackAllocate size -> undefined
--   HeapAllocate con size -> undefined
--   HeapPayload operand -> undefined
--   PointerTag operand -> undefined
--   Offset offset operand -> undefined
--   Copy dst src size -> undefined
--   Store dst src repr -> undefined
--   Load src repr -> undefined
