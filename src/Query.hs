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

import Protolude hiding (IntMap, put, get)

import Control.Monad.Fail
import Data.Constraint.Extras.TH
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import Data.Persist as Persist
import Data.Some (Some(Some))
import Rock

import qualified Applicative.Syntax as Applicative
import Binding (Binding)
import qualified ClosureConverted.Syntax as ClosureConverted
import Extra
import qualified FileSystem
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
import qualified Occurrences.Intervals as Occurrences
import qualified Position
import qualified Surface.Syntax as Surface
import qualified Query.Mapped as Mapped
import Scope (Scope)
import qualified Scope
import qualified Span
import qualified Core.Syntax as Syntax
import Syntax.Telescope (Telescope)

data Query a where
  SourceDirectories :: Query [FileSystem.Directory]
  InputFiles :: Query (HashSet FilePath)
  FileText :: FilePath -> Query Text
  ModuleFile :: Name.Module -> Query (Maybe FilePath)
  ParsedFile :: FilePath -> Query (Name.Module, Module.Header, [(Position.Absolute, (Name, Surface.Definition))])
  ModuleHeader :: Name.Module -> Query Module.Header
  ImportedNames :: Name.Module -> Mapped.Query Name.Pre Scope.Entry a -> Query a
  NameAliases :: Name.Module -> Query (HashMap Name.QualifiedConstructor (HashSet Name.Pre), HashMap Name.Qualified (HashSet Name.Pre))
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ModuleSpanMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Span.Absolute)
  ParsedDefinition :: Name.Module -> Mapped.Query (Scope.Key, Name) Surface.Definition a -> Query a
  Scopes :: Name.Module -> Query ((Scope, Scope, Scope.Visibility), Scope.Module)
  ResolvedName :: Scope.KeyedName -> Name.Pre -> Query (Maybe Scope.Entry)
  IsDefinitionVisible :: Scope.KeyedName -> Name.Qualified -> Query Bool
  ElaboratingDefinition :: Scope.KeyedName -> Query (Maybe (Syntax.Definition, Syntax.Type Void, Meta.Vars (Syntax.Term Void)))
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void))
  ConstructorType :: Name.QualifiedConstructor -> Query (Telescope Binding Syntax.Type Syntax.Type Void)
  KeyedNamePosition :: Scope.KeyedName -> Query (FilePath, Position.Absolute)
  Occurrences :: Scope.KeyedName -> Query Occurrences.Intervals

  LambdaLifted :: Name.Qualified -> Query (LambdaLifted.Definition, IntMap Int (Telescope Name LambdaLifted.Type LambdaLifted.Term Void))
  LambdaLiftedDefinition :: Name.Lifted -> Query (Maybe LambdaLifted.Definition)
  ClosureConverted :: Name.Lifted -> Query (Maybe ClosureConverted.Definition)
  ClosureConvertedType :: Name.Lifted -> Query (ClosureConverted.Type Void)
  ClosureConvertedConstructorType :: Name.QualifiedConstructor -> Query (Telescope Name ClosureConverted.Type ClosureConverted.Type Void)
  Applicative :: Name.Lifted -> Query (Maybe Applicative.Definition)
  ConstructorTag :: Name.QualifiedConstructor -> Query (Maybe Int)

fetchImportedName
  :: MonadFetch Query m
  => Name.Module
  -> Name.Pre
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
      ModuleHeader a -> h 5 a
      ImportedNames a b -> h 6 (a, b)
      NameAliases a -> h 7 a
      ParsedDefinition a b -> h 8 (a, b)
      ModulePositionMap a -> h 9 a
      ModuleSpanMap a -> h 10 a
      Scopes a -> h 11 a
      ResolvedName a b -> h 12 (a, b)
      IsDefinitionVisible a b -> h 13 (a, b)
      ElaboratingDefinition a -> h 14 a
      ElaboratedType a -> h 15 a
      ElaboratedDefinition a -> h 16 a
      ConstructorType a -> h 17 a
      KeyedNamePosition a -> h 18 a
      Occurrences a -> h 19 a
      LambdaLifted a -> h 20 a
      LambdaLiftedDefinition a -> h 21 a
      ClosureConverted a -> h 22 a
      ClosureConvertedType a -> h 23 a
      ClosureConvertedConstructorType a -> h 24 a
      Applicative a -> h 25 a
      ConstructorTag a -> h 26 a
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
      5 -> Some . ModuleHeader <$> get
      6 -> (\(x, Some y) -> Some $ ImportedNames x y) <$> get
      7 -> Some . NameAliases <$> get
      8 -> (\(x, Some y) -> Some $ ParsedDefinition x y) <$> get
      9 -> Some . ModulePositionMap <$> get
      10 -> Some . ModuleSpanMap <$> get
      11 -> Some . Scopes <$> get
      12 -> Some . uncurry ResolvedName <$> get
      13 -> Some . uncurry IsDefinitionVisible <$> get
      14 -> Some . ElaboratingDefinition <$> get
      15 -> Some . ElaboratedType <$> get
      16 -> Some . ElaboratedDefinition <$> get
      17 -> Some . ConstructorType <$> get
      18 -> Some . KeyedNamePosition <$> get
      19 -> Some . Occurrences <$> get
      20 -> Some . LambdaLifted <$> get
      21 -> Some . LambdaLiftedDefinition <$> get
      22 -> Some . ClosureConverted <$> get
      23 -> Some . ClosureConvertedType <$> get
      24 -> Some . ClosureConvertedConstructorType <$> get
      25 -> Some . Applicative <$> get
      26 -> Some . ConstructorTag <$> get
      _ -> fail "Persist (Some Query): no such tag"

  put (Some query) =
    case query of
      SourceDirectories -> p 0 ()
      InputFiles -> p 1 ()
      FileText a -> p 2 a
      ModuleFile a -> p 3 a
      ParsedFile a -> p 4 a
      ModuleHeader a -> p 5 a
      ImportedNames a b -> p 6 (a, Some b)
      NameAliases a -> p 7 a
      ParsedDefinition a b -> p 8 (a, Some b)
      ModulePositionMap a -> p 9 a
      ModuleSpanMap a -> p 10 a
      Scopes a -> p 11 a
      ResolvedName a b -> p 12 (a, b)
      IsDefinitionVisible a b -> p 13 (a, b)
      ElaboratingDefinition a -> p 14 a
      ElaboratedType a -> p 15 a
      ElaboratedDefinition a -> p 16 a
      ConstructorType a -> p 17 a
      KeyedNamePosition a -> p 18 a
      Occurrences a -> p 19 a
      LambdaLifted a -> p 20 a
      LambdaLiftedDefinition a -> p 21 a
      ClosureConverted a -> p 22 a
      ClosureConvertedType a -> p 23 a
      ClosureConvertedConstructorType a -> p 24 a
      Applicative a -> p 25 a
      ConstructorTag a -> p 26 a
      -- Don't forget to add a case to `get` above!
    where
      p :: Persist a => Word8 -> a -> Put ()
      p tag a = do
        put tag
        put a
