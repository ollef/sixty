{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Assembly where

import Data.Persist
import Literal (Literal)
import qualified Literal
import qualified Name
import Prettyprinter
import Protolude hiding (Type, local, moduleName)

data Local = Local !Int !NameSuggestion
  deriving (Eq, Ord, Show, Generic, Hashable, Persist)

newtype NameSuggestion = NameSuggestion Text
  deriving stock (Show, Generic)
  deriving newtype (IsString, Persist, Semigroup, Monoid)

data Operand
  = LocalOperand !Local
  | GlobalConstant !Name.Lifted !Type
  | GlobalFunction !Name.Lifted !(Return Type) [Type]
  | StructOperand [Operand]
  | Lit !Literal
  deriving (Show, Generic, Persist, Hashable)

data Type
  = Word
  | WordPointer
  | FunctionPointer !(Return Type) [Type]
  | Struct [Type]
  deriving (Eq, Show, Generic, Persist, Hashable)

data Return a = Void | Return a
  deriving (Eq, Show, Generic, Persist, Hashable, Foldable, Traversable, Functor)

data Instruction
  = Copy !Operand !Operand !Operand
  | Call !(Return (Type, Local)) !Operand [(Type, Operand)]
  | Load !Local !Operand
  | Store !Operand !Operand
  | InitGlobal !Name.Lifted !Type !Operand
  | Add !Local !Operand !Operand
  | Sub !Local !Operand !Operand
  | Mul !Local !Operand !Operand
  | AddPointer !Local !Operand !Operand
  | StackAllocate !Local !Operand
  | SaveStack !Local
  | RestoreStack !Operand
  | HeapAllocate
      { destination :: !Local
      , shadowStack :: !Operand
      , heapPointer :: !Operand
      , heapLimit :: !Operand
      , constructorTag :: !Word8
      , size :: !Operand
      }
  | ExtractHeapPointer !Local !Operand
  | ExtractHeapPointerConstructorTag !Local !Operand
  | ExtractValue !Local !Operand !Int
  | Switch !(Return (Type, Local)) !Operand [(Integer, BasicBlock)] BasicBlock
  deriving (Show, Generic, Persist, Hashable)

data Definition
  = KnownConstantDefinition !Type !Literal !Bool
  | ConstantDefinition !Type !(Return Type) [(Type, Local)] BasicBlock
  | FunctionDefinition !(Return Type) [(Type, Local)] BasicBlock
  deriving (Show, Generic, Persist, Hashable)

type StackPointer = Local

data BasicBlock = BasicBlock [Instruction] !(Return Operand)
  deriving (Show, Generic, Persist, Hashable)

instance Applicative Return where
  pure = Return
  Void <*> _ = Void
  _ <*> Void = Void
  Return f <*> Return x = Return $ f x

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
      GlobalConstant global type_ ->
        "(" <> pretty type_ <+> "constant" <+> pretty global <> ")"
      GlobalFunction global return_ arity ->
        "(function " <> pretty return_ <> " (" <> pretty arity <> ")" <+> pretty global <> ")"
      StructOperand operands ->
        "{" <> hsep (punctuate comma $ pretty <$> operands) <> "}"
      Lit lit ->
        pretty lit

instance Pretty Type where
  pretty type_ =
    case type_ of
      Word -> "word"
      WordPointer -> "word*"
      FunctionPointer returnType argTypes -> pretty returnType <+> tupled (pretty <$> argTypes)
      Struct types -> "{" <> hsep (punctuate comma $ pretty <$> types) <> "}"

instance Pretty Instruction where
  pretty instruction =
    case instruction of
      Copy dst src size_ ->
        voidInstr "copy" [dst, src, size_]
      Call (Return dst) fun args ->
        returningInstr dst ("call" <+> pretty fun) args
      Call Void fun args ->
        voidInstr ("call" <+> pretty fun) args
      Load dst src ->
        returningInstr dst "load" [src]
      Store dst src ->
        voidInstr "store" [dst, src]
      InitGlobal dst type_ src ->
        "init" <+> pretty type_ <+> "global" <+> hsep [pretty dst, pretty src]
      Add dst arg1 arg2 ->
        returningInstr dst "add" [arg1, arg2]
      Sub dst arg1 arg2 ->
        returningInstr dst "sub" [arg1, arg2]
      Mul dst arg1 arg2 ->
        returningInstr dst "mul" [arg1, arg2]
      AddPointer dst arg1 arg2 ->
        returningInstr dst "add*" [arg1, arg2]
      StackAllocate dst size_ ->
        returningInstr dst "alloca" [size_]
      SaveStack dst ->
        returningInstr dst "savestack" ([] :: [Operand])
      RestoreStack o ->
        voidInstr "restorestack" [o]
      HeapAllocate dst a b c d e ->
        returningInstr dst "gcmalloc" [a, b, c, Lit $ Literal.Integer $ fromIntegral d, e]
      ExtractHeapPointer dst a ->
        returningInstr dst "extract heap pointer" [a]
      ExtractHeapPointerConstructorTag dst a ->
        returningInstr dst "extract heap pointer" [a]
      ExtractValue dst struct index ->
        pretty dst <+> "=" <+> "extractvalue" <+> hsep [pretty struct, pretty index]
      Switch result scrutinee branches default_ ->
        case result of
          Void -> ""
          Return local -> pretty local <+> "= "
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

instance Pretty Definition where
  pretty definition =
    case definition of
      KnownConstantDefinition type_ knownConstant _isConstant ->
        "known" <+> pretty type_ <+> "constant" <+> "=" <> line
          <> indent 2 (pretty knownConstant)
      ConstantDefinition type_ returnType constantParameters basicBlock ->
        pretty type_ <+> "constant" <+> pretty returnType <+> tupled (pretty <$> constantParameters) <+> "=" <> line
          <> indent 2 (pretty basicBlock)
      FunctionDefinition returnType args basicBlock ->
        "function" <+> pretty returnType <+> tupled (pretty <$> args) <+> "=" <> line
          <> indent 2 (pretty basicBlock)

instance Pretty BasicBlock where
  pretty (BasicBlock instrs result) =
    vsep
      [ vsep $ pretty <$> instrs
      , pretty result
      ]

instance Pretty a => Pretty (Return a) where
  pretty voided = case voided of
    Void -> "void"
    Return a -> pretty a

-------------------------------------------------------------------------------

nameText :: Name.Lifted -> Text
nameText name =
  case name of
    Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) 0 ->
      moduleName <> "." <> name_
    Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) i ->
      moduleName <> "." <> name_ <> "$" <> show i
