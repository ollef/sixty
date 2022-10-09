{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LLVM.Orphans.Hashable where

import Data.Hashable
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

deriving instance Hashable LLVM.AST.AddrSpace.AddrSpace

deriving instance Hashable LLVM.AST.BasicBlock

deriving instance Hashable LLVM.AST.COMDAT.SelectionKind

deriving instance Hashable LLVM.AST.CallingConvention.CallingConvention

deriving instance Hashable LLVM.AST.Constant.Constant

deriving instance Hashable LLVM.AST.DLL.StorageClass

deriving instance Hashable LLVM.AST.DataLayout.AlignType

deriving instance Hashable LLVM.AST.DataLayout.AlignmentInfo

deriving instance Hashable LLVM.AST.DataLayout.DataLayout

deriving instance Hashable LLVM.AST.DataLayout.Endianness

deriving instance Hashable LLVM.AST.DataLayout.Mangling

deriving instance Hashable LLVM.AST.Definition

deriving instance Hashable LLVM.AST.FastMathFlags

deriving instance Hashable LLVM.AST.Float.SomeFloat

deriving instance Hashable LLVM.AST.FloatingPointPredicate.FloatingPointPredicate

deriving instance Hashable LLVM.AST.FloatingPointType

deriving instance Hashable LLVM.AST.FunctionAttribute.FunctionAttribute

deriving instance Hashable LLVM.AST.FunctionAttribute.GroupID

deriving instance Hashable LLVM.AST.Global

deriving instance Hashable LLVM.AST.InlineAssembly.Dialect

deriving instance Hashable LLVM.AST.InlineAssembly.InlineAssembly

deriving instance Hashable LLVM.AST.Instruction

deriving instance Hashable LLVM.AST.IntegerPredicate.IntegerPredicate

deriving instance Hashable LLVM.AST.LandingPadClause

deriving instance Hashable LLVM.AST.Linkage.Linkage

deriving instance Hashable LLVM.AST.MDNode

deriving instance Hashable LLVM.AST.MemoryOrdering

deriving instance Hashable LLVM.AST.Metadata

deriving instance Hashable LLVM.AST.MetadataNodeID

deriving instance Hashable LLVM.AST.Module

deriving instance Hashable LLVM.AST.Name

deriving instance Hashable LLVM.AST.Operand.BasicTypeTag

deriving instance Hashable LLVM.AST.Operand.ChecksumInfo

deriving instance Hashable LLVM.AST.Operand.ChecksumKind

deriving instance Hashable LLVM.AST.Operand.DIAccessibility

deriving instance Hashable LLVM.AST.Operand.DIBasicType

deriving instance Hashable LLVM.AST.Operand.DICompileUnit

deriving instance Hashable LLVM.AST.Operand.DICompositeType

deriving instance Hashable LLVM.AST.Operand.DICount

deriving instance Hashable LLVM.AST.Operand.DIDerivedType

deriving instance Hashable LLVM.AST.Operand.DIEnumerator

deriving instance Hashable LLVM.AST.Operand.DIExpression

deriving instance Hashable LLVM.AST.Operand.DIFile

deriving instance Hashable LLVM.AST.Operand.DIFlag

deriving instance Hashable LLVM.AST.Operand.DIGlobalVariable

deriving instance Hashable LLVM.AST.Operand.DIGlobalVariableExpression

deriving instance Hashable LLVM.AST.Operand.DIImportedEntity

deriving instance Hashable LLVM.AST.Operand.DIInheritance

deriving instance Hashable LLVM.AST.Operand.DILexicalBlockBase

deriving instance Hashable LLVM.AST.Operand.DILocalScope

deriving instance Hashable LLVM.AST.Operand.DILocalVariable

deriving instance Hashable LLVM.AST.Operand.DILocation

deriving instance Hashable LLVM.AST.Operand.DIMacroInfo

deriving instance Hashable LLVM.AST.Operand.DIMacroNode

deriving instance Hashable LLVM.AST.Operand.DIModule

deriving instance Hashable LLVM.AST.Operand.DINamespace

deriving instance Hashable LLVM.AST.Operand.DINode

deriving instance Hashable LLVM.AST.Operand.DIObjCProperty

deriving instance Hashable LLVM.AST.Operand.DIScope

deriving instance Hashable LLVM.AST.Operand.DISubprogram

deriving instance Hashable LLVM.AST.Operand.DISubrange

deriving instance Hashable LLVM.AST.Operand.DISubroutineType

deriving instance Hashable LLVM.AST.Operand.DITemplateParameter

deriving instance Hashable LLVM.AST.Operand.DIType

deriving instance Hashable LLVM.AST.Operand.DIVariable

deriving instance Hashable LLVM.AST.Operand.DWOp

deriving instance Hashable LLVM.AST.Operand.DWOpFragment

deriving instance Hashable LLVM.AST.Operand.DebugEmissionKind

deriving instance Hashable LLVM.AST.Operand.DebugNameTableKind

deriving instance Hashable LLVM.AST.Operand.DerivedTypeTag

deriving instance Hashable LLVM.AST.Operand.Encoding

deriving instance Hashable LLVM.AST.Operand.ImportedEntityTag

deriving instance Hashable LLVM.AST.Operand.Operand

deriving instance Hashable LLVM.AST.Operand.TemplateValueParameterTag

deriving instance Hashable LLVM.AST.Operand.Virtuality

deriving instance Hashable LLVM.AST.Parameter

deriving instance Hashable LLVM.AST.ParameterAttribute.ParameterAttribute

deriving instance Hashable LLVM.AST.RMWOperation.RMWOperation

deriving instance Hashable LLVM.AST.SynchronizationScope

deriving instance Hashable LLVM.AST.TailCallKind

deriving instance Hashable LLVM.AST.Terminator

deriving instance Hashable LLVM.AST.ThreadLocalStorage.Model

deriving instance Hashable LLVM.AST.Type

deriving instance Hashable LLVM.AST.UnnamedAddr

deriving instance Hashable LLVM.AST.Visibility.Visibility

deriving instance Hashable a => Hashable (LLVM.AST.MDRef a)

deriving instance Hashable a => Hashable (LLVM.AST.Named a)
