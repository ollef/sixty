{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Orphans where

import Data.Constraint.Extras
import Data.Dependent.HashMap (DHashMap)
import qualified Data.Dependent.HashMap as DHashMap
import Data.GADT.Compare (GEq)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntervalMap.FingerTree (IntervalMap)
import qualified Data.IntervalMap.FingerTree as IntervalMap
import qualified Data.Map as Map
import Data.Persist
import qualified Data.Set as Set
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
import Protolude hiding (IntMap, IntSet, get, put)
import Rock.Traces

instance (Persist k, Persist v, Coercible Int k) => Persist (IntMap k v) where
  put =
    put . IntMap.toList

  get =
    IntMap.fromList <$> get

instance (Persist k, Coercible Int k) => Persist (IntSet k) where
  put =
    put . IntSet.toList

  get =
    IntSet.fromList <$> get

instance (Persist k, Eq k, Hashable k, Persist v) => Persist (HashMap k v) where
  put =
    put . HashMap.toList

  get =
    HashMap.fromList <$> get

instance (Persist a, Eq a, Hashable a) => Persist (HashSet a) where
  put =
    put . HashSet.toList

  get =
    HashSet.fromList <$> get

instance Persist k => Persist (IntervalMap.Interval k) where
  put (IntervalMap.Interval a b) =
    put (a, b)

  get =
    uncurry IntervalMap.Interval <$> get

instance (Persist k, Ord k, Persist v) => Persist (IntervalMap k v) where
  put m =
    put $
      fold $
        (`IntervalMap.intersections` m)
          <$> IntervalMap.bounds m

  get =
    mconcat . map (uncurry IntervalMap.singleton) <$> get

instance Hashable k => Hashable (IntervalMap.Interval k) where
  hashWithSalt s (IntervalMap.Interval a b) =
    hashWithSalt s (a, b)

instance (Hashable k, Ord k, Hashable v) => Hashable (IntervalMap k v) where
  hashWithSalt s m =
    hashWithSalt s $
      (`IntervalMap.intersections` m)
        <$> IntervalMap.bounds m

instance (Persist v, GEq k, Hashable (DHashMap.Some k), Persist (DHashMap.Some k), Has' Persist k dep) => Persist (ValueDeps k dep v) where
  put (ValueDeps a b) = do
    put a
    put b

  get =
    ValueDeps <$> get <*> get

instance (Persist (DHashMap.Some k), Has' Persist k f, GEq k, Hashable (DHashMap.Some k)) => Persist (DHashMap k f) where
  put m = do
    put @Int $ DHashMap.size m
    forM_ (DHashMap.toList m) $ \(k DHashMap.:=> f) ->
      has' @Persist @f k (put f)

  get =
    DHashMap.fromList <$> do
      n <- get @Int
      replicateM n $ do
        DHashMap.Some k <- get
        f <- has' @Persist @f k get
        pure $ k DHashMap.:=> f

instance Persist a => Persist (Identity a) where
  put (Identity a) =
    put a

  get =
    Identity <$> get

instance Persist a => Persist (Const a b) where
  put (Const a) =
    put a

  get =
    Const <$> get

instance (Hashable k, Hashable v) => Hashable (Map k v) where
  hashWithSalt s = hashWithSalt s . Map.toList

instance (Hashable k) => Hashable (Set k) where
  hashWithSalt s = hashWithSalt s . Set.toList

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
