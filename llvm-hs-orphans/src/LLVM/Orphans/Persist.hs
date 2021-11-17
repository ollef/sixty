{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LLVM.Orphans.Persist where

import Data.Persist
import qualified LLVM.AST
import qualified LLVM.AST.AddrSpace
import qualified LLVM.AST.COMDAT
import qualified LLVM.AST.CallingConvention
import qualified LLVM.AST.Constant
import qualified LLVM.AST.DLL
import qualified LLVM.AST.DataLayout
import qualified LLVM.AST.Float
import qualified LLVM.AST.FloatingPointPredicate
import qualified LLVM.AST.FunctionAttribute
import qualified LLVM.AST.InlineAssembly
import qualified LLVM.AST.IntegerPredicate
import qualified LLVM.AST.Linkage
import qualified LLVM.AST.Operand
import qualified LLVM.AST.ParameterAttribute
import qualified LLVM.AST.RMWOperation
import qualified LLVM.AST.ThreadLocalStorage
import qualified LLVM.AST.Visibility
import LLVM.Orphans.Hashable ()

deriving instance Persist LLVM.AST.AddrSpace.AddrSpace

deriving instance Persist LLVM.AST.BasicBlock

deriving instance Persist LLVM.AST.COMDAT.SelectionKind

deriving instance Persist LLVM.AST.CallingConvention.CallingConvention

deriving instance Persist LLVM.AST.Constant.Constant

deriving instance Persist LLVM.AST.DLL.StorageClass

deriving instance Persist LLVM.AST.DataLayout.AlignType

deriving instance Persist LLVM.AST.DataLayout.AlignmentInfo

deriving instance Persist LLVM.AST.DataLayout.DataLayout

deriving instance Persist LLVM.AST.DataLayout.Endianness

deriving instance Persist LLVM.AST.DataLayout.Mangling

deriving instance Persist LLVM.AST.Definition

deriving instance Persist LLVM.AST.FastMathFlags

deriving instance Persist LLVM.AST.Float.SomeFloat

deriving instance Persist LLVM.AST.FloatingPointPredicate.FloatingPointPredicate

deriving instance Persist LLVM.AST.FloatingPointType

deriving instance Persist LLVM.AST.FunctionAttribute.FunctionAttribute

deriving instance Persist LLVM.AST.FunctionAttribute.GroupID

deriving instance Persist LLVM.AST.Global

deriving instance Persist LLVM.AST.InlineAssembly.Dialect

deriving instance Persist LLVM.AST.InlineAssembly.InlineAssembly

deriving instance Persist LLVM.AST.Instruction

deriving instance Persist LLVM.AST.IntegerPredicate.IntegerPredicate

deriving instance Persist LLVM.AST.LandingPadClause

deriving instance Persist LLVM.AST.Linkage.Linkage

deriving instance Persist LLVM.AST.MDNode

deriving instance Persist LLVM.AST.MemoryOrdering

deriving instance Persist LLVM.AST.Metadata

deriving instance Persist LLVM.AST.MetadataNodeID

deriving instance Persist LLVM.AST.Module

deriving instance Persist LLVM.AST.Name

deriving instance Persist LLVM.AST.Operand.BasicTypeTag

deriving instance Persist LLVM.AST.Operand.ChecksumInfo

deriving instance Persist LLVM.AST.Operand.ChecksumKind

deriving instance Persist LLVM.AST.Operand.DIAccessibility

deriving instance Persist LLVM.AST.Operand.DIBasicType

deriving instance Persist LLVM.AST.Operand.DICompileUnit

deriving instance Persist LLVM.AST.Operand.DICompositeType

deriving instance Persist LLVM.AST.Operand.DICount

deriving instance Persist LLVM.AST.Operand.DIDerivedType

deriving instance Persist LLVM.AST.Operand.DIEnumerator

deriving instance Persist LLVM.AST.Operand.DIExpression

deriving instance Persist LLVM.AST.Operand.DIFile

deriving instance Persist LLVM.AST.Operand.DIFlag

deriving instance Persist LLVM.AST.Operand.DIGlobalVariable

deriving instance Persist LLVM.AST.Operand.DIGlobalVariableExpression

deriving instance Persist LLVM.AST.Operand.DIImportedEntity

deriving instance Persist LLVM.AST.Operand.DIInheritance

deriving instance Persist LLVM.AST.Operand.DILexicalBlockBase

deriving instance Persist LLVM.AST.Operand.DILocalScope

deriving instance Persist LLVM.AST.Operand.DILocalVariable

deriving instance Persist LLVM.AST.Operand.DILocation

deriving instance Persist LLVM.AST.Operand.DIMacroInfo

deriving instance Persist LLVM.AST.Operand.DIMacroNode

deriving instance Persist LLVM.AST.Operand.DIModule

deriving instance Persist LLVM.AST.Operand.DINamespace

deriving instance Persist LLVM.AST.Operand.DINode

deriving instance Persist LLVM.AST.Operand.DIObjCProperty

deriving instance Persist LLVM.AST.Operand.DIScope

deriving instance Persist LLVM.AST.Operand.DISubprogram

deriving instance Persist LLVM.AST.Operand.DISubrange

deriving instance Persist LLVM.AST.Operand.DISubroutineType

deriving instance Persist LLVM.AST.Operand.DITemplateParameter

deriving instance Persist LLVM.AST.Operand.DIType

deriving instance Persist LLVM.AST.Operand.DIVariable

deriving instance Persist LLVM.AST.Operand.DWOp

deriving instance Persist LLVM.AST.Operand.DWOpFragment

deriving instance Persist LLVM.AST.Operand.DebugEmissionKind

deriving instance Persist LLVM.AST.Operand.DebugNameTableKind

deriving instance Persist LLVM.AST.Operand.DerivedTypeTag

deriving instance Persist LLVM.AST.Operand.Encoding

deriving instance Persist LLVM.AST.Operand.ImportedEntityTag

deriving instance Persist LLVM.AST.Operand.Operand

deriving instance Persist LLVM.AST.Operand.TemplateValueParameterTag

deriving instance Persist LLVM.AST.Operand.Virtuality

deriving instance Persist LLVM.AST.Parameter

deriving instance Persist LLVM.AST.ParameterAttribute.ParameterAttribute

deriving instance Persist LLVM.AST.RMWOperation.RMWOperation

deriving instance Persist LLVM.AST.SynchronizationScope

deriving instance Persist LLVM.AST.TailCallKind

deriving instance Persist LLVM.AST.Terminator

deriving instance Persist LLVM.AST.ThreadLocalStorage.Model

deriving instance Persist LLVM.AST.Type

deriving instance Persist LLVM.AST.UnnamedAddr

deriving instance Persist LLVM.AST.Visibility.Visibility

deriving instance Persist a => Persist (LLVM.AST.MDRef a)

deriving instance Persist a => Persist (LLVM.AST.Named a)
