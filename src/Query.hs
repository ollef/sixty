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
{-# language UndecidableInstances #-}
{-# options_ghc -Wno-unused-matches #-} -- deriveGShow triggers this for some reason
module Query where

import Protolude hiding (IntMap, put, get)

import Control.Monad.Fail
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import Data.Persist as Persist
import Rock

import qualified ClosureConverted.Syntax as ClosureConverted
import HashTag
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
import qualified FileSystem
import qualified Occurrences.Intervals as Occurrences
import PersistTag
import qualified Position
import qualified Presyntax
import qualified Query.Mapped as Mapped
import Scope (Scope)
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)

data Query a where
  SourceDirectories :: Query [FileSystem.Directory]
  InputFiles :: Query (HashSet FilePath)
  FileText :: FilePath -> Query Text
  ModuleFile :: Name.Module -> Query (Maybe FilePath)
  ParsedFile :: FilePath -> Query (Name.Module, Module.Header, [(Position.Absolute, (Name, Presyntax.Definition))])
  ModuleHeader :: Name.Module -> Query Module.Header
  ImportedNames :: Name.Module -> Mapped.Query Name.Pre Scope.Entry a -> Query a
  NameAliases :: Name.Module -> Query (HashMap Name.QualifiedConstructor (HashSet Name.Pre), HashMap Name.Qualified (HashSet Name.Pre))
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ModuleSpanMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Span.Absolute)
  ParsedDefinition :: Name.Module -> Mapped.Query (Scope.Key, Name) Presyntax.Definition a -> Query a
  Scopes :: Name.Module -> Query ((Scope, Scope, Scope.Visibility), Scope.Module)
  ResolvedName :: Scope.KeyedName -> Name.Pre -> Query (Maybe Scope.Entry)
  IsDefinitionVisible :: Scope.KeyedName -> Name.Qualified -> Query Bool
  ElaboratingDefinition :: Scope.KeyedName -> Query (Maybe (Syntax.Definition, Syntax.Type Void, Meta.Vars (Syntax.Term Void)))
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void))
  ConstructorType :: Name.QualifiedConstructor -> Query (Telescope Syntax.Type Syntax.Type Void)
  KeyedNameSpan :: Scope.KeyedName -> Query (FilePath, Span.Absolute)
  Occurrences :: Scope.KeyedName -> Query Occurrences.Intervals

  LambdaLifted :: Name.Qualified -> Query (Maybe (LambdaLifted.Definition, IntMap Int (Telescope LambdaLifted.Type LambdaLifted.Term Void)))
  LambdaLiftedDefinition :: Name.Lifted -> Query (Maybe LambdaLifted.Definition)
  ClosureConverted :: Name.Lifted -> Query (Maybe ClosureConverted.Definition)
  ClosureConvertedType :: Name.Lifted -> Query (ClosureConverted.Type Void)
  ClosureConvertedConstructorType :: Name.QualifiedConstructor -> Query (Telescope ClosureConverted.Type ClosureConverted.Type Void)

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

instance Eq a => EqTag Query (Const a) where
  eqTagged _ _ (Const a) (Const a') =
    a == a'

instance HashTag Query where
  hashTagged query =
    case query of
      SourceDirectories {} -> hash
      InputFiles {} -> hash
      FileText {} -> hash
      ModuleFile {} -> hash
      ParsedFile {} -> hash
      ModuleHeader {} -> hash
      ImportedNames _ q -> hashTagged q
      NameAliases {} -> hash
      ParsedDefinition _ q -> hashTagged q
      ModulePositionMap {} -> hash
      ModuleSpanMap {} -> hash
      Scopes {} -> hash
      ResolvedName {} -> hash
      IsDefinitionVisible {} -> hash
      ElaboratingDefinition {} -> hash
      ElaboratedType {} -> hash
      ElaboratedDefinition {} -> hash
      ConstructorType {} -> hash
      KeyedNameSpan {} -> hash
      Occurrences {} -> hash
      LambdaLifted {} -> hash
      LambdaLiftedDefinition {} -> hash
      ClosureConverted {} -> hash
      ClosureConvertedType {} -> hash
      ClosureConvertedConstructorType {} -> hash

instance Persist (DMap.Some Query) where
  get = do
    n <- get @Word8
    case n of
      0 -> pure $ DMap.This SourceDirectories
      1 -> pure $ DMap.This InputFiles
      2 -> DMap.This . FileText <$> get
      3 -> DMap.This . ModuleFile <$> get
      4 -> DMap.This . ParsedFile <$> get
      5 -> DMap.This . ModuleHeader <$> get
      6 -> (\(x, DMap.This y) -> DMap.This $ ImportedNames x y) <$> get
      7 -> DMap.This . NameAliases <$> get
      8 -> (\(x, DMap.This y) -> DMap.This $ ParsedDefinition x y) <$> get
      9 -> DMap.This . ModulePositionMap <$> get
      10 -> DMap.This . ModuleSpanMap <$> get
      11 -> DMap.This . Scopes <$> get
      12 -> DMap.This . uncurry ResolvedName <$> get
      13 -> DMap.This . uncurry IsDefinitionVisible <$> get
      14 -> DMap.This . ElaboratingDefinition <$> get
      15 -> DMap.This . ElaboratedType <$> get
      16 -> DMap.This . ElaboratedDefinition <$> get
      17 -> DMap.This . ConstructorType <$> get
      18 -> DMap.This . KeyedNameSpan <$> get
      19 -> DMap.This . Occurrences <$> get
      20 -> DMap.This . LambdaLifted <$> get
      21 -> DMap.This . LambdaLiftedDefinition <$> get
      22 -> DMap.This . ClosureConverted <$> get
      23 -> DMap.This . ClosureConvertedType <$> get
      24 -> DMap.This . ClosureConvertedConstructorType <$> get
      _ -> fail "Persist (Some Query): no such tag"

  put (DMap.This query) =
    case query of
      SourceDirectories -> p 0 ()
      InputFiles -> p 1 ()
      FileText a -> p 2 a
      ModuleFile a -> p 3 a
      ParsedFile a -> p 4 a
      ModuleHeader a -> p 5 a
      ImportedNames a b -> p 6 (a, DMap.This b)
      NameAliases a -> p 7 a
      ParsedDefinition a b -> p 8 (a, DMap.This b)
      ModulePositionMap a -> p 9 a
      ModuleSpanMap a -> p 10 a
      Scopes a -> p 11 a
      ResolvedName a b -> p 12 (a, b)
      IsDefinitionVisible a b -> p 13 (a, b)
      ElaboratingDefinition a -> p 14 a
      ElaboratedType a -> p 15 a
      ElaboratedDefinition a -> p 16 a
      ConstructorType a -> p 17 a
      KeyedNameSpan a -> p 18 a
      Occurrences a -> p 19 a
      LambdaLifted a -> p 20 a
      LambdaLiftedDefinition a -> p 21 a
      ClosureConverted a -> p 22 a
      ClosureConvertedType a -> p 23 a
      ClosureConvertedConstructorType a -> p 24 a
      -- Don't forget to add a case above!
    where
      p :: Persist a => Word8 -> a -> Put ()
      p tag a = do
        put tag
        put a

instance (forall a. Persist a => Persist (f a)) => PersistTag Query f where
  putTagged query =
    case query of
      SourceDirectories {} -> put
      InputFiles {} -> put
      FileText {} -> put
      ModuleFile {} -> put
      ParsedFile {} -> put
      ModuleHeader {} -> put
      ImportedNames _ q -> putTagged q
      NameAliases {} -> put
      ParsedDefinition _ q -> putTagged q
      ModulePositionMap {} -> put
      ModuleSpanMap {} -> put
      Scopes {} -> put
      ResolvedName {} -> put
      IsDefinitionVisible {} -> put
      ElaboratingDefinition {} -> put
      ElaboratedType {} -> put
      ElaboratedDefinition {} -> put
      ConstructorType {} -> put
      KeyedNameSpan {} -> put
      Occurrences {} -> put
      LambdaLifted {} -> put
      LambdaLiftedDefinition {} -> put
      ClosureConverted {} -> put
      ClosureConvertedType {} -> put
      ClosureConvertedConstructorType {} -> put

  getTagged query =
    case query of
      SourceDirectories {} -> get
      InputFiles {} -> get
      FileText {} -> get
      ModuleFile {} -> get
      ParsedFile {} -> get
      ModuleHeader {} -> get
      ImportedNames _ q -> getTagged q
      NameAliases {} -> get
      ParsedDefinition _ q -> getTagged q
      ModulePositionMap {} -> get
      ModuleSpanMap {} -> get
      Scopes {} -> get
      ResolvedName {} -> get
      IsDefinitionVisible {} -> get
      ElaboratingDefinition {} -> get
      ElaboratedType {} -> get
      ElaboratedDefinition {} -> get
      ConstructorType {} -> get
      KeyedNameSpan {} -> get
      Occurrences {} -> get
      LambdaLifted {} -> get
      LambdaLiftedDefinition {} -> get
      ClosureConverted {} -> get
      ClosureConvertedType {} -> get
      ClosureConvertedConstructorType {} -> get
