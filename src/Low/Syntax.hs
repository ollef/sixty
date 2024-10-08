{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module Low.Syntax where

import Index (Index, Scope)
import qualified Index
import Literal (Literal)
import Low.PassBy (PassBy)
import Low.Representation (Representation)
import Name (Name)
import qualified Name
import Protolude

data Term v
  = Operand !(Operand v)
  | Let !PassBy !Name !(LetOperation v) !(Scope Term v)
  | Seq !(SeqOperation v) !(Term v)
  deriving (Eq, Show, Generic, Hashable)

data LetOperation v
  = Case !(Operand v) [Branch v] (Maybe (Term v))
  | Call !Name.Lowered [Operand v]
  | StackAllocate !(Operand v)
  | HeapAllocate !Name.QualifiedConstructor !(Operand v)
  | HeapPayload !(Operand v)
  | PointerTag !(Operand v)
  | Offset !(Operand v) !(Operand v)
  | Load !(Operand v) !Representation
  deriving (Eq, Show, Generic, Hashable)

data SeqOperation v
  = Store !(Operand v) !(Operand v) !Representation
  | Copy !(Operand v) !(Operand v) !(Operand v)
  | IncreaseReferenceCount !(Operand v) !Representation
  | IncreaseReferenceCounts !(Operand v) !(Operand v)
  | DecreaseReferenceCount !(Operand v) !Representation
  deriving (Eq, Show, Generic, Hashable)

data Operand v
  = Var !(Index v)
  | Global !Representation !Name.Lowered
  | Literal !Literal
  | Representation !Representation
  | Tag !Name.QualifiedConstructor
  | Undefined !Representation
  deriving (Eq, Show, Generic, Hashable)

data Branch v
  = ConstructorBranch !Name.QualifiedConstructor !(Term v)
  | LiteralBranch !Literal !(Term v)
  deriving (Eq, Show, Generic, Hashable)

branchTerm :: Branch v -> Term v
branchTerm = \case
  ConstructorBranch _ t -> t
  LiteralBranch _ t -> t

data Function v
  = Body !PassBy !(Term v)
  | Parameter !Name !PassBy !(Scope Function v)
  deriving (Eq, Show, Generic, Hashable)

type Type = Term

data Definition
  = ConstantDefinition !Representation
  | FunctionDefinition !(Function Index.Zero)
  deriving (Eq, Show, Generic, Hashable)

data Signature
  = ConstantSignature !Representation
  | FunctionSignature [PassBy] !PassBy
  deriving (Eq, Show, Generic, Hashable)
