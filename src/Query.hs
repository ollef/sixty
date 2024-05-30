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
-- Comes from deriveArgDict
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Query where

import Boxity
import qualified ClosureConverted.Syntax as ClosureConverted
import Core.Binding (Binding)
import qualified Core.Syntax as Syntax
import qualified Data.ByteString.Lazy as Lazy
import Data.Constraint.Extras.TH
import Data.EnumMap (EnumMap)
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.OrderedHashSet (OrderedHashSet)
import Data.Some (Some (Some))
import Data.Text.Utf16.Rope (Rope)
import qualified Elaboration.Meta
import Extra
import qualified FileSystem
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Low.Syntax
import qualified Low.Syntax as Low
import qualified Module
import Name (Name)
import qualified Name
import qualified Occurrences.Intervals as Occurrences
import qualified Position
import Protolude hiding (get, put)
import qualified Query.Mapped as Mapped
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
  LowSignature :: Name.Lifted -> Query Low.Syntax.Signature
  LoweredDefinitions :: Name.Lifted -> Query [(Name.Lowered, Low.Syntax.Definition)]
  ConstructorRepresentations :: Name.Qualified -> Query (Boxity, Maybe (HashMap Name.Constructor Int))
  ConstructorRepresentation :: Name.QualifiedConstructor -> Query (Boxity, Maybe Int)
  LowDefinitions :: Name.Lifted -> Query [(Name.Lowered, Low.Definition)]
  LowModule :: Name.Module -> Query [(Name.Lowered, Low.Definition)]
  LLVMModule :: Name.Module -> Query Lazy.ByteString
  LLVMModuleInitModule :: Query Lazy.ByteString

fetchImportedName
  :: (MonadFetch Query m)
  => Name.Module
  -> Name.Surface
  -> m (Maybe Scope.Entry)
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
      LowSignature a -> h 29 a
      LoweredDefinitions a -> h 30 a
      ConstructorRepresentations a -> h 31 a
      ConstructorRepresentation a -> h 32 a
      LowDefinitions a -> h 33 a
      LowModule a -> h 34 a
      LLVMModule a -> h 35 a
      LLVMModuleInitModule -> h 36 ()
    where
      {-# INLINE h #-}
      h :: (Hashable b) => Int -> b -> Int
      h tag payload =
        hash tag `hashWithSalt` payload

instance Hashable (Some Query) where
  {-# INLINE hash #-}
  hash (Some query) =
    hash query

  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (Some query) =
    hashWithSalt salt query
