{-# language DeriveAnyClass #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language QuantifiedConstraints #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}
{-# options_ghc -Wno-unused-matches #-} -- deriveGShow triggers this for some reason
module Query where

import qualified Assembly
import qualified ClosureConverted.Syntax as ClosureConverted
import Control.Monad.Fail
import Core.Binding (Binding)
import qualified Elaboration.Meta
import qualified Core.Syntax as Syntax
import qualified CPSAssembly
import Data.Constraint.Extras.TH
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import Data.OrderedHashSet (OrderedHashSet)
import Data.Persist as Persist
import Data.Some (Some(Some))
import Extra
import qualified FileSystem
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified LLVM.AST as LLVM
import qualified Module
import Name (Name)
import qualified Name
import qualified Occurrences.Intervals as Occurrences
import qualified Position
import Protolude hiding (IntMap, put, get)
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
  FileText :: FilePath -> Query ByteString
  ModuleFile :: Name.Module -> Query (Maybe FilePath)
  ParsedFile :: FilePath -> Query (Name.Module, Module.Header, [(Position.Absolute, (Name, Surface.Definition))])
  ModuleDefinitions :: Name.Module -> Query (OrderedHashSet Name)
  ModuleHeader :: Name.Module -> Query Module.Header
  ImportedNames :: Name.Module -> Mapped.Query Name.Surface Scope.Entry a -> Query a
  NameAliases :: Name.Module -> Query (HashMap Name.QualifiedConstructor (HashSet Name.Surface), HashMap Name.Qualified (HashSet Name.Surface))
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ModuleSpanMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Span.Absolute)
  ParsedDefinition :: Name.Module -> Mapped.Query (Scope.Key, Name) Surface.Definition a -> Query a
  Scopes :: Name.Module -> Query ((Scope, Scope, Scope.Visibility), Scope.Module)
  ResolvedName :: Scope.KeyedName -> Name.Surface -> Query (Maybe Scope.Entry)
  IsDefinitionVisible :: Scope.KeyedName -> Name.Qualified -> Query Bool
  ElaboratingDefinition :: Scope.KeyedName -> Query (Maybe (Syntax.Definition, Syntax.Type Void, Elaboration.Meta.EagerState))
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void))
  ConstructorType :: Name.QualifiedConstructor -> Query (Telescope Binding Syntax.Type Syntax.Type Void)
  KeyedNamePosition :: Scope.KeyedName -> Query (FilePath, Position.Absolute)
  Occurrences :: Scope.KeyedName -> Query Occurrences.Intervals

  LambdaLifted :: Name.Qualified -> Query (LambdaLifted.Definition, IntMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void))
  LambdaLiftedDefinition :: Name.Lifted -> Query (Maybe LambdaLifted.Definition)
  LambdaLiftedModuleDefinitions :: Name.Module -> Query (OrderedHashSet Name.Lifted)

  ClosureConverted :: Name.Lifted -> Query (Maybe ClosureConverted.Definition)
  ClosureConvertedType :: Name.Lifted -> Query (ClosureConverted.Type Void)
  ClosureConvertedConstructorType :: Name.QualifiedConstructor -> Query (Telescope Name ClosureConverted.Type ClosureConverted.Type Void)
  ClosureConvertedSignature :: Name.Lifted -> Query (Maybe Representation.Signature)
  ConstructorTag :: Name.QualifiedConstructor -> Query (Maybe Int)

  Assembly :: Name.Lifted -> Query (Maybe (Assembly.Definition Assembly.BasicBlock, Int))
  CPSAssembly :: Name.Lifted -> Query [(Assembly.Name, CPSAssembly.Definition)]
  CPSAssemblyModule :: Name.Module -> Query [(Assembly.Name, CPSAssembly.Definition)]
  LLVMModule :: Name.Module -> Query LLVM.Module
  LLVMModuleInitModule :: Query LLVM.Module

fetchImportedName
  :: MonadFetch Query m
  => Name.Module
  -> Name.Surface
  -> m (Maybe Scope.Entry)
fetchImportedName module_ =
  fetch . ImportedNames module_ . Mapped.Query

deriving instance Show (Query a)

deriveGEq ''Query
deriveGCompare ''Query
deriveGShow ''Query
deriveArgDict ''Query

instance Hashable (Query a) where
  {-# inline hashWithSalt #-}
  hashWithSalt =
    defaultHashWithSalt
  hash query =
    case query of
      SourceDirectories -> h 0 ()
      InputFiles -> h 1 ()
      FileText a -> h 2 a
      ModuleFile a -> h 3 a
      ParsedFile a -> h 4 a
      ModuleDefinitions a -> h 5 a
      ModuleHeader a -> h 6 a
      ImportedNames a b -> h 7 (a, b)
      NameAliases a -> h 8 a
      ParsedDefinition a b -> h 9 (a, b)
      ModulePositionMap a -> h 10 a
      ModuleSpanMap a -> h 11 a
      Scopes a -> h 12 a
      ResolvedName a b -> h 13 (a, b)
      IsDefinitionVisible a b -> h 14 (a, b)
      ElaboratingDefinition a -> h 15 a
      ElaboratedType a -> h 16 a
      ElaboratedDefinition a -> h 17 a
      ConstructorType a -> h 18 a
      KeyedNamePosition a -> h 19 a
      Occurrences a -> h 20 a
      LambdaLifted a -> h 21 a
      LambdaLiftedDefinition a -> h 22 a
      LambdaLiftedModuleDefinitions a -> h 23 a
      ClosureConverted a -> h 24 a
      ClosureConvertedType a -> h 25 a
      ClosureConvertedConstructorType a -> h 26 a
      ClosureConvertedSignature a -> h 27 a
      ConstructorTag a -> h 28 a
      Assembly a -> h 29 a
      CPSAssembly a -> h 30 a
      CPSAssemblyModule a -> h 31 a
      LLVMModule a -> h 32 a
      LLVMModuleInitModule -> h 33 ()
    where
      {-# inline h #-}
      h :: Hashable a => Int -> a -> Int
      h tag payload =
        hash tag `hashWithSalt` payload

instance Hashable (Some Query) where
  {-# inline hash #-}
  hash (Some query) =
    hash query

  {-# inline hashWithSalt #-}
  hashWithSalt salt (Some query) =
    hashWithSalt salt query

instance Persist (Some Query) where
  get = do
    n <- get @Word8
    case n of
      0 -> pure $ Some SourceDirectories
      1 -> pure $ Some InputFiles
      2 -> Some . FileText <$> get
      3 -> Some . ModuleFile <$> get
      4 -> Some . ParsedFile <$> get
      5 -> Some . ModuleDefinitions <$> get
      6 -> Some . ModuleHeader <$> get
      7 -> (\(x, Some y) -> Some $ ImportedNames x y) <$> get
      8 -> Some . NameAliases <$> get
      9 -> (\(x, Some y) -> Some $ ParsedDefinition x y) <$> get
      10 -> Some . ModulePositionMap <$> get
      11 -> Some . ModuleSpanMap <$> get
      12 -> Some . Scopes <$> get
      13 -> Some . uncurry ResolvedName <$> get
      14 -> Some . uncurry IsDefinitionVisible <$> get
      15 -> Some . ElaboratingDefinition <$> get
      16 -> Some . ElaboratedType <$> get
      17 -> Some . ElaboratedDefinition <$> get
      18 -> Some . ConstructorType <$> get
      19 -> Some . KeyedNamePosition <$> get
      20 -> Some . Occurrences <$> get
      21 -> Some . LambdaLifted <$> get
      22 -> Some . LambdaLiftedDefinition <$> get
      23 -> Some . LambdaLiftedModuleDefinitions <$> get
      24 -> Some . ClosureConverted <$> get
      25 -> Some . ClosureConvertedType <$> get
      26 -> Some . ClosureConvertedConstructorType <$> get
      27 -> Some . ClosureConvertedSignature <$> get
      28 -> Some . ConstructorTag <$> get
      29 -> Some . Assembly <$> get
      30 -> Some . CPSAssembly <$> get
      31 -> Some . CPSAssemblyModule <$> get
      32 -> Some . LLVMModule <$> get
      33 -> pure $ Some LLVMModuleInitModule
      _ -> fail "Persist (Some Query): no such tag"

  put (Some query) =
    case query of
      SourceDirectories -> p 0 ()
      InputFiles -> p 1 ()
      FileText a -> p 2 a
      ModuleFile a -> p 3 a
      ParsedFile a -> p 4 a
      ModuleDefinitions a -> p 5 a
      ModuleHeader a -> p 6 a
      ImportedNames a b -> p 7 (a, Some b)
      NameAliases a -> p 8 a
      ParsedDefinition a b -> p 9 (a, Some b)
      ModulePositionMap a -> p 10 a
      ModuleSpanMap a -> p 11 a
      Scopes a -> p 12 a
      ResolvedName a b -> p 13 (a, b)
      IsDefinitionVisible a b -> p 14 (a, b)
      ElaboratingDefinition a -> p 15 a
      ElaboratedType a -> p 16 a
      ElaboratedDefinition a -> p 17 a
      ConstructorType a -> p 18 a
      KeyedNamePosition a -> p 19 a
      Occurrences a -> p 20 a
      LambdaLifted a -> p 21 a
      LambdaLiftedDefinition a -> p 22 a
      LambdaLiftedModuleDefinitions a -> p 23 a
      ClosureConverted a -> p 24 a
      ClosureConvertedType a -> p 25 a
      ClosureConvertedConstructorType a -> p 26 a
      ClosureConvertedSignature a -> p 27 a
      ConstructorTag a -> p 28 a
      Assembly a -> p 29 a
      CPSAssembly a -> p 30 a
      CPSAssemblyModule a -> p 31 a
      LLVMModule a -> p 32 a
      LLVMModuleInitModule -> p 33 ()
      -- Don't forget to add a case to `get` above!
    where
      p :: Persist a => Word8 -> a -> Put ()
      p tag a = do
        put tag
        put a
