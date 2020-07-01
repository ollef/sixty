{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language OverloadedStrings #-}
module CPSAssembly where

import Assembly (Local, Operand)
import qualified Assembly 
import Data.Persist
import Data.Text.Prettyprint.Doc
import qualified Name
import Protolude

data Instruction
  = Copy !Operand !Operand !Operand
  | Load !Local !Operand
  | Store !Operand !Operand
  | SetUndefined !Operand !Operand
  | InitGlobal !Name.Lifted !Operand
  | Add !Local !Operand !Operand
  | Sub !Local !Operand !Operand
  | HeapAllocate !Local !Operand
  deriving (Show, Generic, Hashable, Persist)

data Terminator
  = Switch !Operand [(Int, Terminator)] Terminator
  | TailCall !Operand [Operand]
  deriving (Show, Generic, Hashable, Persist)

data BasicBlock = BasicBlock [Instruction] !Terminator
  deriving (Show, Generic, Hashable, Persist)

type Definition = Assembly.Definition BasicBlock

instance Pretty Instruction where
  pretty instruction =
    case instruction of
      Copy dst src size ->
        voidInstr "copy" [dst, src, size]

      Load dst src ->
        returningInstr dst "load" [src]

      Store dst src ->
        voidInstr "store" [dst, src]

      SetUndefined dst size ->
        voidInstr "set undefined" [dst, size]

      InitGlobal dst src ->
        "init global" <+> hsep [pretty dst, pretty src]

      Add dst arg1 arg2 ->
        returningInstr dst "add" [arg1, arg2]

      Sub dst arg1 arg2 ->
        returningInstr dst "sub" [arg1, arg2]

      HeapAllocate dst size ->
        returningInstr dst "gcmalloc" [size]
    where
      voidInstr name args =
        name <+> hsep (pretty <$> args)

      returningInstr ret name args =
        pretty ret <+> "=" <+> voidInstr name args

instance Pretty Terminator where
  pretty terminator =
    case terminator of
      TailCall fun args ->
        "tail call" <+> pretty fun <> tupled (pretty <$> args)

      Switch scrutinee branches default_ ->
        "switch" <+> pretty scrutinee <> line <>
          indent 2
            (vsep
              [ pretty i <+> "->" <> line <>
                indent 2 (pretty basicBlock)
              | (i, basicBlock) <- branches
              ] <> line <>
              "_ -> " <> line <> indent 2 (pretty default_)
            )

instance Pretty BasicBlock where
  pretty (BasicBlock instrs terminator) =
    vsep $ (pretty <$> instrs) <> [pretty terminator]
