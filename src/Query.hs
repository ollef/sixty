{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Query where

import qualified Assembly
import Boxity
import qualified ClosureConverted.Syntax as ClosureConverted
import Control.Monad.Fail
import Core.Binding (Binding)
import qualified Core.Syntax as Syntax
import Data.Constraint.Extras.TH
import Data.EnumMap (EnumMap)
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.OrderedHashSet (OrderedHashSet)
import Data.Persist as Persist
import Data.Some (Some (Some))
import Data.Text.Utf16.Rope (Rope)
import qualified Elaboration.Meta
import Extra
import qualified FileSystem
import qualified LLVM.AST as LLVM
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Module
import Name (Name)
import qualified Name
import qualified Occurrences.Intervals as Occurrences
import qualified Position
import Protolude hiding (get, put)
import qualified Query.Mapped as Mapped
import qualified Representation
import Rock
import Scope (Scope)
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface
import Telescope (Telescope)

data Query a where
  SourceDirectories :: Query [FileSystem.Directory]
  InputFiles :: Query (HashSet FilePath)
  FileText :: FilePath -> Query Text
  FileRope :: FilePath -> Query Rope
  ModuleFile :: Name.Module -> Query (Maybe FilePath)
  ParsedFile :: FilePath -> Query (Name.Module, Module.Header, [(Position.Absolute, (Name, Surface.Definition))])
  ModuleDefinitions :: Name.Module -> Query (OrderedHashSet Name)
  ModuleHeader :: Name.Module -> Query Module.Header
  ImportedNames :: Name.Module -> Mapped.Query Name.Surface Scope.Entry a -> Query a
  NameAliases :: Name.Module -> Query (HashMap Name.QualifiedConstructor (HashSet Name.Surface), HashMap Name.Qualified (HashSet Name.Surface))
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.DefinitionKind, Name) Position.Absolute)
  ModuleSpanMap :: Name.Module -> Query (HashMap (Scope.DefinitionKind, Name) Span.Absolute)
  ParsedDefinition :: Name.Module -> Mapped.Query (Scope.DefinitionKind, Name) Surface.Definition a -> Query a
  ModuleScope :: Name.Module -> Query (Scope, Scope)
  ResolvedName :: Name.Module -> Name.Surface -> Query (Maybe Scope.Entry)
  ElaboratingDefinition :: Scope.DefinitionKind -> Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void, Elaboration.Meta.EagerState))
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Syntax.Definition, Syntax.Type Void)
  Dependencies :: Name.Qualified -> Mapped.Query Name.Qualified () a -> Query a
  TransitiveDependencies :: Name.Qualified -> Mapped.Query Name.Qualified () a -> Query a
  ConstructorType :: Name.QualifiedConstructor -> Query (Telescope Binding Syntax.Type Syntax.Type Void)
  DefinitionPosition :: Scope.DefinitionKind -> Name.Qualified -> Query (FilePath, Maybe Position.Absolute)
  Occurrences :: Scope.DefinitionKind -> Name.Qualified -> Query Occurrences.Intervals
  LambdaLifted :: Name.Qualified -> Query (LambdaLifted.Definition, EnumMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void))
  LambdaLiftedDefinition :: Name.Lifted -> Query LambdaLifted.Definition
  LambdaLiftedModuleDefinitions :: Name.Module -> Query (OrderedHashSet Name.Lifted)
  ClosureConverted :: Name.Lifted -> Query ClosureConverted.Definition
  ClosureConvertedType :: Name.Lifted -> Query (ClosureConverted.Type Void)
  ClosureConvertedConstructorType :: Name.QualifiedConstructor -> Query (Telescope Name ClosureConverted.Type ClosureConverted.Type Void)
  ClosureConvertedSignature :: Name.Lifted -> Query Representation.Signature
  ConstructorRepresentations :: Name.Qualified -> Query (Boxity, Maybe (HashMap Name.Constructor Int))
  ConstructorRepresentation :: Name.QualifiedConstructor -> Query (Boxity, Maybe Int)
  Assembly :: Name.Lifted -> Query (Maybe Assembly.Definition)
  HeapAllocates :: Name.Lifted -> Query Bool
  AssemblyModule :: Name.Module -> Query [(Name.Lifted, Assembly.Definition)]
  LLVMModule :: Name.Module -> Query LLVM.Module
  LLVMModuleInitModule :: Query LLVM.Module

fetchImportedName ::
  MonadFetch Query m =>
  Name.Module ->
  Name.Surface ->
  m (Maybe Scope.Entry)
fetchImportedName module_ =
  fetch . ImportedNames module_ . Mapped.Query

deriving instance Eq (Query a)

deriving instance Show (Query a)

deriveGEq ''Query
deriveGCompare ''Query
deriveGShow ''Query
deriveArgDict ''Query

instance Hashable (Query a) where
  {-# INLINE hashWithSalt #-}
  hashWithSalt =
    defaultHashWithSalt
  hash query =
    case query of
      SourceDirectories -> h 0 ()
      InputFiles -> h 1 ()
      FileText a -> h 2 a
      FileRope a -> h 3 a
      ModuleFile a -> h 4 a
      ParsedFile a -> h 5 a
      ModuleDefinitions a -> h 6 a
      ModuleHeader a -> h 7 a
      ImportedNames a b -> h 8 (a, b)
      NameAliases a -> h 9 a
      ModulePositionMap a -> h 10 a
      ModuleSpanMap a -> h 11 a
      ParsedDefinition a b -> h 12 (a, b)
      ModuleScope a -> h 13 a
      ResolvedName a b -> h 14 (a, b)
      ElaboratingDefinition a b -> h 15 (a, b)
      ElaboratedType a -> h 16 a
      ElaboratedDefinition a -> h 17 a
      Dependencies a b -> h 18 (a, b)
      TransitiveDependencies a b -> h 19 (a, b)
      ConstructorType a -> h 20 a
      DefinitionPosition a b -> h 21 (a, b)
      Occurrences a b -> h 22 (a, b)
      LambdaLifted a -> h 23 a
      LambdaLiftedDefinition a -> h 24 a
      LambdaLiftedModuleDefinitions a -> h 25 a
      ClosureConverted a -> h 26 a
      ClosureConvertedType a -> h 27 a
      ClosureConvertedConstructorType a -> h 28 a
      ClosureConvertedSignature a -> h 29 a
      ConstructorRepresentations a -> h 30 a
      ConstructorRepresentation a -> h 31 a
      Assembly a -> h 32 a
      HeapAllocates a -> h 33 a
      AssemblyModule a -> h 34 a
      LLVMModule a -> h 35 a
      LLVMModuleInitModule -> h 36 ()
    where
      {-# INLINE h #-}
      h :: Hashable b => Int -> b -> Int
      h tag payload =
        hash tag `hashWithSalt` payload

instance Hashable (Some Query) where
  {-# INLINE hash #-}
  hash (Some query) =
    hash query

  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (Some query) =
    hashWithSalt salt query

instance Persist (Some Query) where
  get = do
    n <- get @Word8
    case n of
      0 -> pure $ Some SourceDirectories
      1 -> pure $ Some InputFiles
      2 -> Some . FileText <$> get
      3 -> Some . FileRope <$> get
      4 -> Some . ModuleFile <$> get
      5 -> Some . ParsedFile <$> get
      6 -> Some . ModuleDefinitions <$> get
      7 -> Some . ModuleHeader <$> get
      8 -> (\(x, Some y) -> Some $ ImportedNames x y) <$> get
      9 -> Some . NameAliases <$> get
      10 -> Some . ModulePositionMap <$> get
      11 -> Some . ModuleSpanMap <$> get
      12 -> (\(x, Some y) -> Some $ ParsedDefinition x y) <$> get
      13 -> Some . ModuleScope <$> get
      14 -> Some . uncurry ResolvedName <$> get
      15 -> (\(x, y) -> Some $ ElaboratingDefinition x y) <$> get
      16 -> Some . ElaboratedType <$> get
      17 -> Some . ElaboratedDefinition <$> get
      18 -> (\(x, Some y) -> Some $ Dependencies x y) <$> get
      19 -> (\(x, Some y) -> Some $ TransitiveDependencies x y) <$> get
      20 -> Some . ConstructorType <$> get
      21 -> (\(x, y) -> Some $ DefinitionPosition x y) <$> get
      22 -> (\(x, y) -> Some $ Occurrences x y) <$> get
      23 -> Some . LambdaLifted <$> get
      24 -> Some . LambdaLiftedDefinition <$> get
      25 -> Some . LambdaLiftedModuleDefinitions <$> get
      26 -> Some . ClosureConverted <$> get
      27 -> Some . ClosureConvertedType <$> get
      28 -> Some . ClosureConvertedConstructorType <$> get
      29 -> Some . ClosureConvertedSignature <$> get
      30 -> Some . ConstructorRepresentations <$> get
      31 -> Some . ConstructorRepresentation <$> get
      32 -> Some . Assembly <$> get
      33 -> Some . HeapAllocates <$> get
      34 -> Some . AssemblyModule <$> get
      35 -> Some . LLVMModule <$> get
      36 -> pure $ Some LLVMModuleInitModule
      _ -> fail "Persist (Some Query): no such tag"

  put (Some query) =
    case query of
      SourceDirectories -> p 0 ()
      InputFiles -> p 1 ()
      FileText a -> p 2 a
      FileRope a -> p 3 a
      ModuleFile a -> p 4 a
      ParsedFile a -> p 5 a
      ModuleDefinitions a -> p 6 a
      ModuleHeader a -> p 7 a
      ImportedNames a b -> p 8 (a, Some b)
      NameAliases a -> p 9 a
      ModulePositionMap a -> p 10 a
      ModuleSpanMap a -> p 11 a
      ParsedDefinition a b -> p 12 (a, Some b)
      ModuleScope a -> p 13 a
      ResolvedName a b -> p 14 (a, b)
      ElaboratingDefinition a b -> p 15 (a, b)
      ElaboratedType a -> p 16 a
      ElaboratedDefinition a -> p 17 a
      Dependencies a b -> p 18 (a, Some b)
      TransitiveDependencies a b -> p 19 (a, Some b)
      ConstructorType a -> p 20 a
      DefinitionPosition a b -> p 21 (a, b)
      Occurrences a b -> p 22 (a, b)
      LambdaLifted a -> p 23 a
      LambdaLiftedDefinition a -> p 24 a
      LambdaLiftedModuleDefinitions a -> p 25 a
      ClosureConverted a -> p 26 a
      ClosureConvertedType a -> p 27 a
      ClosureConvertedConstructorType a -> p 28 a
      ClosureConvertedSignature a -> p 29 a
      ConstructorRepresentations a -> p 30 a
      ConstructorRepresentation a -> p 31 a
      Assembly a -> p 32 a
      HeapAllocates a -> p 33 a
      AssemblyModule a -> p 34 a
      LLVMModule a -> p 35 a
      LLVMModuleInitModule -> p 36 ()
    where
      -- Don't forget to add a case to `get` above!

      p :: Persist a => Word8 -> a -> Put ()
      p tag a = do
        put tag
        put a
