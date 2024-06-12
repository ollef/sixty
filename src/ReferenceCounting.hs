{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module ReferenceCounting where

import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import qualified Index.Map
import qualified Index.Map as Index (Map)
import Literal (Literal)
import Low.PassBy (PassBy)
import Low.Representation (Representation)
import qualified Low.Syntax as Syntax
import Monad hiding (State)
import Name (Name)
import qualified Name
import Protolude hiding (evaluate, repr)
import Var (Var)

type Occurrences = EnumSet Var

data WithOccurrences a = WithOccurrences
  { occurrences :: Occurrences
  , payload :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative WithOccurrences where
  pure = WithOccurrences mempty

  WithOccurrences occs1 f <*> WithOccurrences occs2 x = WithOccurrences (occs1 <> occs2) (f x)

type Value = WithOccurrences InnerValue

data InnerValue
  = Operand !Operand
  | Let !PassBy !Name !Var !Value !Value
  | Seq !Value !Value
  | Case !Operand [Branch] (Maybe Value)
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
  = Var !Var
  | Global !Representation !Name.Lowered
  | Literal !Literal
  | Representation !Representation
  | Tag !Name.QualifiedConstructor
  | Undefined !Representation
  deriving (Show)

data Branch
  = ConstructorBranch !Name.QualifiedConstructor !InnerValue
  | LiteralBranch !Literal !InnerValue
  deriving (Show)

evaluate :: Index.Map v Var -> EnumMap Var (EnumSet Var) -> Syntax.Term v -> M (Value, EnumSet Var)
evaluate env parents = \case
  Syntax.Operand operand -> do
    let operand' = evaluateOperand env parents operand
    pure (Operand <$> operand', operand'.occurrences)
  Syntax.Let passBy name term body -> do
    var <- freshVar
    (term', termParents) <- evaluate env parents term
    (body', bodyParents) <-
      evaluate
        (env Index.Map.:> var)
        ( if EnumSet.null termParents
            then parents
            else EnumMap.insert var termParents parents
        )
        body
    pure
      ( WithOccurrences (term'.occurrences <> EnumSet.delete var body'.occurrences) $
          Let passBy name var term' body'
      , EnumSet.delete var bodyParents
      )
  Syntax.Seq lhs rhs -> do
    (lhs', _) <- evaluate env parents lhs
    (rhs', rhsParents) <- evaluate env parents rhs
    pure (WithOccurrences (lhs'.occurrences <> rhs'.occurrences) $ Seq lhs' rhs', rhsParents)
  Syntax.Case scrutinee branches maybeDefaultBranch -> do
    let scrutinee' = evaluateOperand env parents scrutinee
    branches' <- mapM (evaluateBranch env parents) branches
    maybeDefaultBranch' <- mapM (evaluate env parents) maybeDefaultBranch
    pure
      ( WithOccurrences
          ( scrutinee'.occurrences
              <> foldMap ((.occurrences) . fst) branches'
              <> foldMap ((.occurrences) . fst) maybeDefaultBranch'
          )
          $ Case scrutinee'.payload (map ((.payload) . fst) branches') (fst <$> maybeDefaultBranch')
      , foldMap snd branches' <> foldMap snd maybeDefaultBranch'
      )
  Syntax.Call global args -> do
    let args' = map (evaluateOperand env parents) args
    pure (WithOccurrences (foldMap (.occurrences) args') $ Call global (map (.payload) args'), mempty)
  Syntax.StackAllocate size ->
    pure (StackAllocate <$> evaluateOperand env parents size, mempty)
  Syntax.HeapAllocate constr size ->
    pure (HeapAllocate constr <$> evaluateOperand env parents size, mempty)
  Syntax.HeapPayload pointer -> do
    let pointer' = evaluateOperand env parents pointer
    pure (HeapPayload <$> pointer', pointer'.occurrences)
  Syntax.PointerTag pointer ->
    pure (PointerTag <$> evaluateOperand env parents pointer, mempty)
  Syntax.Offset ref size -> do
    let ref' = evaluateOperand env parents ref
    pure (Offset <$> ref' <*> evaluateOperand env parents size, ref'.occurrences)
  Syntax.Copy dst src size ->
    pure (Copy <$> evaluateOperand env parents dst <*> evaluateOperand env parents src <*> evaluateOperand env parents size, mempty)
  Syntax.Store dst src repr ->
    pure (Store <$> evaluateOperand env parents dst <*> evaluateOperand env parents src <*> pure repr, mempty)
  Syntax.Load ref repr ->
    pure (Load <$> evaluateOperand env parents ref <*> pure repr, mempty)

evaluateOperand :: Index.Map v Var -> EnumMap Var (EnumSet Var) -> Syntax.Operand v -> WithOccurrences Operand
evaluateOperand env parents = \case
  Syntax.Var index -> do
    let var = Index.Map.index env index
    WithOccurrences (EnumMap.findWithDefault (EnumSet.singleton var) var parents) $ Var var
  Syntax.Global repr global -> pure $ Global repr global
  Syntax.Literal lit -> pure $ Literal lit
  Syntax.Representation repr -> pure $ Representation repr
  Syntax.Tag constr -> pure $ Tag constr
  Syntax.Undefined repr -> pure $ Undefined repr

evaluateBranch :: Index.Map v Var -> EnumMap Var (EnumSet Var) -> Syntax.Branch v -> M (WithOccurrences Branch, EnumSet Var)
evaluateBranch env parents = \case
  Syntax.LiteralBranch lit branch -> do
    (branch', branchParents) <- evaluate env parents branch
    pure (LiteralBranch lit <$> branch', branchParents)
  Syntax.ConstructorBranch constr branch -> do
    (branch', branchParents) <- evaluate env parents branch
    pure (ConstructorBranch constr <$> branch', branchParents)

data Ownership
  = Borrowed
  | Owned
  deriving (Show)

data ReferenceCountState = ReferenceCountState
  { owned :: EnumMap Var Representation
  , borrowed :: EnumMap Var Representation
  }

type ReferenceCount = State ReferenceCountState

data Provenance
  = Unmanaged
  | Managed !Ownership !Representation
  | DerivedFrom !Var

referenceCount :: Value -> ReferenceCount (Value, Provenance)
referenceCount value = case value.payload of
  Operand operand -> case operand of
    Var var -> do
      rc <- get
      case (EnumMap.lookup var rc.owned, EnumMap.lookup var rc.borrowed) of
        (Nothing, Nothing) -> pure (value, Unmanaged)
        (Just repr, _) -> pure (value, Managed Owned var)
        (Nothing, _) -> pure (value, DerivedFrom var)
    Global _ _ -> pure (value, Unmanaged)
    Literal _ -> pure (value, Unmanaged)
    Representation _ -> pure (value, Unmanaged)
    Tag _ -> pure (value, Unmanaged)
    Undefined _ -> pure (value, Unmanaged)
  Let passBy name var val body -> do
    (val', provenance) <- referenceCount val
    _
  Seq lhs rhs -> do
    owned <- gets (.owned)
    EnumMap.intersection rhs.occurrences
  Case scrutinee branches maybeDefaultBranch -> _
  Call fun args -> _
  StackAllocate size -> _
  HeapAllocate con size -> _
  HeapPayload operand -> _
  PointerTag operand -> _
  Offset offset operand -> _
  Copy dst src size -> _
  Store dst src repr -> _
  Load src repr -> _
