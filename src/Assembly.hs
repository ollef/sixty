{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Assembly where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Persist
import Data.Text.Prettyprint.Doc
import Literal (Literal)
import qualified Name
import Protolude hiding (local, moduleName)
import Representation (Representation)

data Local = Local !Int !NameSuggestion
  deriving (Eq, Ord, Show, Generic, Hashable, Persist)

newtype NameSuggestion = NameSuggestion Text
  deriving stock (Show, Generic)
  deriving newtype (IsString, Persist)

data Operand
  = LocalOperand !Local
  | GlobalConstant !Name.Lifted !Representation
  | GlobalFunction !Name.Lifted !Return !Int
  | Lit !Literal
  deriving (Show, Generic, Persist, Hashable)

data Instruction basicBlock
  = Copy !Operand !Operand !Operand
  | Call !(Voided Local) !Operand [Operand]
  | Load !Local !Operand
  | Store !Operand !Operand
  | InitGlobal !Name.Lifted !Representation !Operand
  | Add !Local !Operand !Operand
  | Sub !Local !Operand !Operand
  | StackAllocate !Local !Operand
  | SaveStack !Local
  | RestoreStack !Operand
  | HeapAllocate !Local !Operand
  | Switch !(Voided Local) !Operand [(Integer, basicBlock)] basicBlock
  deriving (Show, Generic, Persist, Hashable, Functor)

data Definition basicBlock
  = KnownConstantDefinition !Representation !Literal !Bool
  | ConstantDefinition !Representation [Local] basicBlock
  | FunctionDefinition [Local] basicBlock
  deriving (Show, Generic, Persist, Hashable, Functor)

type StackPointer = Local

data BasicBlock = BasicBlock [Instruction BasicBlock] !Result
  deriving (Show, Generic, Persist, Hashable)

type Result = Voided Operand

data Voided a = Void | NonVoid a
  deriving (Show, Generic, Persist, Hashable, Foldable, Traversable, Functor)

data Return = ReturnsVoid | Returns
  deriving (Eq, Show, Generic, Persist, Hashable)

--
-------------------------------------------------------------------------------

instance Eq NameSuggestion where
  _ == _ =
    True

instance Ord NameSuggestion where
  compare _ _ =
    EQ

instance Hashable NameSuggestion where
  hashWithSalt s _ =
    hashWithSalt s ()

instance Pretty Local where
  pretty (Local i (NameSuggestion l)) =
    "%" <> pretty l <> "$" <> pretty i

instance Pretty Operand where
  pretty operand =
    case operand of
      LocalOperand local ->
        pretty local
      GlobalConstant global representation ->
        "(" <> pretty representation <+> "constant" <+> pretty global <> ")"
      GlobalFunction global return_ arity ->
        "(function " <> pretty return_ <> " (" <> pretty arity <> ")" <+> pretty global <> ")"
      Lit lit ->
        pretty lit

instance Pretty Return where
  pretty ReturnsVoid = "void"
  pretty Returns = "value"

instance Pretty basicBlock => Pretty (Instruction basicBlock) where
  pretty instruction =
    case instruction of
      Copy dst src size ->
        voidInstr "copy" [dst, src, size]
      Call (NonVoid dst) fun args ->
        returningInstr dst "call" (fun : args)
      Call Void fun args ->
        voidInstr "call" (fun : args)
      Load dst src ->
        returningInstr dst "load" [src]
      Store dst src ->
        voidInstr "store" [dst, src]
      InitGlobal dst representation src ->
        "init" <+> pretty representation <+> "global" <+> hsep [pretty dst, pretty src]
      Add dst arg1 arg2 ->
        returningInstr dst "add" [arg1, arg2]
      Sub dst arg1 arg2 ->
        returningInstr dst "sub" [arg1, arg2]
      StackAllocate dst size ->
        returningInstr dst "alloca" [size]
      SaveStack dst ->
        returningInstr dst "savestack" ([] :: [Operand])
      RestoreStack o ->
        voidInstr "restorestack" [o]
      HeapAllocate dst size ->
        returningInstr dst "gcmalloc" [size]
      Switch result scrutinee branches default_ ->
        case result of
          Void -> ""
          NonVoid local -> pretty local <+> "= "
          <> "switch" <+> pretty scrutinee
          <> line
          <> indent
            2
            ( vsep
                [ pretty i <+> "->" <> line
                  <> indent 2 (pretty basicBlock)
                | (i, basicBlock) <- branches
                ]
                <> line
                <> "_ -> "
                <> line
                <> indent 2 (pretty default_)
            )
    where
      voidInstr name args =
        name <+> hsep (pretty <$> args)

      returningInstr ret name args =
        pretty ret <+> "=" <+> voidInstr name args

instance (Pretty basicBlock) => Pretty (Definition basicBlock) where
  pretty definition =
    case definition of
      KnownConstantDefinition representation knownConstant _isConstant ->
        "known" <+> pretty representation <+> "constant" <+> "=" <> line
          <> indent 2 (pretty knownConstant)
      ConstantDefinition representation constantParameters basicBlock ->
        pretty representation <+> "constant" <+> tupled (pretty <$> constantParameters) <+> "=" <> line
          <> indent 2 (pretty basicBlock)
      FunctionDefinition args basicBlock ->
        "function" <+> tupled (pretty <$> args) <+> "=" <> line
          <> indent 2 (pretty basicBlock)

instance Pretty BasicBlock where
  pretty (BasicBlock instrs result) =
    vsep
      [ vsep $ pretty <$> instrs
      , pretty result
      ]

instance Pretty a => Pretty (Voided a) where
  pretty voided = case voided of
    Void -> "void"
    NonVoid a -> pretty a

-------------------------------------------------------------------------------

nameText :: Name.Lifted -> Text
nameText name =
  case name of
    Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) 0 ->
      moduleName <> "." <> name_
    Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) i ->
      moduleName <> "." <> name_ <> "$" <> show i

-------------------------------------------------------------------------------

data BasicBlockWithOccurrences
  = Nil !Result
  | Cons (HashSet Local, HashSet Local) (Instruction BasicBlockWithOccurrences) BasicBlockWithOccurrences

cons :: Instruction BasicBlockWithOccurrences -> BasicBlockWithOccurrences -> BasicBlockWithOccurrences
cons instruction basicBlock =
  Cons (instructionLocals instruction <> basicBlockLocals basicBlock) instruction basicBlock

basicBlockWithOccurrences :: BasicBlock -> BasicBlockWithOccurrences
basicBlockWithOccurrences (BasicBlock instructions result) =
  case instructions of
    [] ->
      Nil result
    instruction : instructions' ->
      cons
        (basicBlockWithOccurrences <$> instruction)
        (basicBlockWithOccurrences $ Assembly.BasicBlock instructions' result)

basicBlockOccurrences :: BasicBlockWithOccurrences -> HashSet Local
basicBlockOccurrences basicBlock = do
  let (bound, free) =
        basicBlockLocals basicBlock
  free `HashSet.difference` bound

basicBlockLocals :: BasicBlockWithOccurrences -> (HashSet Local, HashSet Local)
basicBlockLocals basicBlock =
  case basicBlock of
    Nil result ->
      resultLocals result
    Cons locals _ _ ->
      locals

resultLocals :: Result -> (HashSet Local, HashSet Local)
resultLocals result =
  case result of
    Void ->
      mempty
    NonVoid operand ->
      operandLocals operand

instructionLocals :: Instruction BasicBlockWithOccurrences -> (HashSet Local, HashSet Local)
instructionLocals instruction =
  case instruction of
    Copy o1 o2 o3 ->
      operandLocals o1 <> operandLocals o2 <> operandLocals o3
    Call (NonVoid l) o os ->
      (HashSet.singleton l, mempty) <> operandLocals o <> foldMap operandLocals os
    Call Void o os ->
      operandLocals o <> foldMap operandLocals os
    Load l o ->
      (HashSet.singleton l, mempty) <> operandLocals o
    Store o1 o2 ->
      operandLocals o1 <> operandLocals o2
    InitGlobal _ _ o ->
      operandLocals o
    Add l o1 o2 ->
      (HashSet.singleton l, mempty) <> operandLocals o1 <> operandLocals o2
    Sub l o1 o2 ->
      (HashSet.singleton l, mempty) <> operandLocals o1 <> operandLocals o2
    StackAllocate l o ->
      (HashSet.singleton l, mempty) <> operandLocals o
    SaveStack l ->
      (HashSet.singleton l, mempty)
    RestoreStack o ->
      operandLocals o
    HeapAllocate l o ->
      (HashSet.singleton l, mempty) <> operandLocals o
    Switch (NonVoid l) o brs d ->
      (HashSet.singleton l, mempty) <> operandLocals o <> foldMap (basicBlockLocals . snd) brs <> basicBlockLocals d
    Switch Void o brs d ->
      operandLocals o <> foldMap (basicBlockLocals . snd) brs <> basicBlockLocals d

operandLocals :: Operand -> (HashSet Local, HashSet Local)
operandLocals operand =
  case operand of
    LocalOperand local ->
      (mempty, HashSet.singleton local)
    GlobalConstant _ _ ->
      mempty
    GlobalFunction {} ->
      mempty
    Lit _ ->
      mempty
