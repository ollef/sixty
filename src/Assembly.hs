{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Assembly where

import Data.Persist
import Data.Text.Prettyprint.Doc
import Literal (Literal)
import qualified Name
import Protolude hiding (Type, local, moduleName)

data Local = Local !Int !NameSuggestion
  deriving (Eq, Ord, Show, Generic, Hashable, Persist)

newtype NameSuggestion = NameSuggestion Text
  deriving stock (Show, Generic)
  deriving newtype (IsString, Persist, Semigroup, Monoid)

data Operand
  = LocalOperand !Local
  | GlobalConstant !Name.Lifted !Type
  | GlobalFunction !Name.Lifted !ReturnType [Type]
  | Lit !Literal
  deriving (Show, Generic, Persist, Hashable)

data Type
  = Word
  | WordPointer
  deriving (Eq, Show, Generic, Persist, Hashable)

data ReturnType = ReturnsVoid | Returns !Type
  deriving (Eq, Show, Generic, Persist, Hashable)

data Instruction
  = Copy !Operand !Operand !Operand
  | Call !(Voided (Type, Local)) !Operand [(Type, Operand)]
  | Load !Local !Operand
  | Store !Operand !Operand
  | InitGlobal !Name.Lifted !Type !Operand
  | Add !Local !Operand !Operand
  | AddPointer !Local !Operand !Operand
  | StackAllocate !Local !Operand
  | SaveStack !Local
  | RestoreStack !Operand
  | HeapAllocate !Local !Operand
  | Switch !(Voided (Type, Local)) !Operand [(Integer, BasicBlock)] BasicBlock
  deriving (Show, Generic, Persist, Hashable)

data Definition
  = KnownConstantDefinition !Type !Literal !Bool
  | ConstantDefinition !Type [(Type, Local)] BasicBlock
  | FunctionDefinition !ReturnType [(Type, Local)] BasicBlock
  deriving (Show, Generic, Persist, Hashable)

type StackPointer = Local

data BasicBlock = BasicBlock [Instruction] !Result
  deriving (Show, Generic, Persist, Hashable)

type Result = Voided Operand

data Voided a = Void | NonVoid a
  deriving (Show, Generic, Persist, Hashable, Foldable, Traversable, Functor)

instance Applicative Voided where
  pure = NonVoid
  Void <*> _ = Void
  _ <*> Void = Void
  NonVoid f <*> NonVoid x = NonVoid $ f x

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
      Lit lit ->
        pretty lit

instance Pretty Type where
  pretty type_ =
    case type_ of
      Word -> "word"
      WordPointer -> "word*"

instance Pretty ReturnType where
  pretty ReturnsVoid = "void"
  pretty (Returns type_) = pretty type_

instance Pretty Instruction where
  pretty instruction =
    case instruction of
      Copy dst src size ->
        voidInstr "copy" [dst, src, size]
      Call (NonVoid dst) fun args ->
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
      AddPointer dst arg1 arg2 ->
        returningInstr dst "add*" [arg1, arg2]
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

instance Pretty Definition where
  pretty definition =
    case definition of
      KnownConstantDefinition representation knownConstant _isConstant ->
        "known" <+> pretty representation <+> "constant" <+> "=" <> line
          <> indent 2 (pretty knownConstant)
      ConstantDefinition representation constantParameters basicBlock ->
        pretty representation <+> "constant" <+> tupled (pretty <$> constantParameters) <+> "=" <> line
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
