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
module Query where

import Protolude hiding (IntMap, put, get)

import Control.Monad.Fail
import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum
import Data.GADT.Compare.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import Data.Persist as Persist
import Rock

import qualified ClosureConverted.Syntax as ClosureConverted
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
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
  InputFiles :: Query [FilePath]
  FileText :: FilePath -> Query Text
  ModuleFile :: Mapped.Query Name.Module FilePath a -> Query a
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

instance (forall a. Eq a => Eq (f a)) => EqTag Query f where
  eqTagged query _ =
    case query of
      InputFiles {} -> (==)
      FileText {} -> (==)
      ModuleFile q -> eqTagged q q
      ParsedFile {} -> (==)
      ModuleHeader {} -> (==)
      ImportedNames _ q -> eqTagged q q
      NameAliases {} -> (==)
      ParsedDefinition _ q -> eqTagged q q
      ModulePositionMap {} -> (==)
      ModuleSpanMap {} -> (==)
      Scopes {} -> (==)
      ResolvedName {} -> (==)
      IsDefinitionVisible {} -> (==)
      ElaboratingDefinition {} -> (==)
      ElaboratedType {} -> (==)
      ElaboratedDefinition {} -> (==)
      ConstructorType {} -> (==)
      KeyedNameSpan {} -> (==)
      Occurrences {} -> (==)
      LambdaLifted {} -> (==)
      LambdaLiftedDefinition {} -> (==)
      ClosureConverted {} -> (==)
      ClosureConvertedType {} -> (==)
      ClosureConvertedConstructorType {} -> (==)

instance Persist (DMap.Some Query) where
  get = do
    n <- get @Word8
    case n of
      0 -> pure $ DMap.This InputFiles
      1 -> DMap.This . FileText <$> get
      2 -> (\(DMap.This x) -> DMap.This $ ModuleFile x) <$> get
      3 -> DMap.This . ParsedFile <$> get
      4 -> DMap.This . ModuleHeader <$> get
      5 -> (\(x, DMap.This y) -> DMap.This $ ImportedNames x y) <$> get
      6 -> DMap.This . NameAliases <$> get
      7 -> (\(x, DMap.This y) -> DMap.This $ ParsedDefinition x y) <$> get
      8 -> DMap.This . ModulePositionMap <$> get
      9 -> DMap.This . ModuleSpanMap <$> get
      10 -> DMap.This . Scopes <$> get
      11 -> DMap.This . uncurry ResolvedName <$> get
      12 -> DMap.This . uncurry IsDefinitionVisible <$> get
      13 -> DMap.This . ElaboratingDefinition <$> get
      14 -> DMap.This . ElaboratedType <$> get
      15 -> DMap.This . ElaboratedDefinition <$> get
      16 -> DMap.This . ConstructorType <$> get
      17 -> DMap.This . KeyedNameSpan <$> get
      18 -> DMap.This . Occurrences <$> get
      19 -> DMap.This . LambdaLifted <$> get
      20 -> DMap.This . LambdaLiftedDefinition <$> get
      21 -> DMap.This . ClosureConverted <$> get
      22 -> DMap.This . ClosureConvertedType <$> get
      23 -> DMap.This . ClosureConvertedConstructorType <$> get
      _ -> fail "Persist (Some Query): no such tag"

  put (DMap.This query) =
    case query of
      InputFiles -> p 0 ()
      FileText a -> p 1 a
      ModuleFile a -> p 2 $ DMap.This a
      ParsedFile a -> p 3 a
      ModuleHeader a -> p 4 a
      ImportedNames a b -> p 5 (a, DMap.This b)
      NameAliases a -> p 6 a
      ParsedDefinition a b -> p 7 (a, DMap.This b)
      ModulePositionMap a -> p 8 a
      ModuleSpanMap a -> p 9 a
      Scopes a -> p 10 a
      ResolvedName a b -> p 11 (a, b)
      IsDefinitionVisible a b -> p 12 (a, b)
      ElaboratingDefinition a -> p 13 a
      ElaboratedType a -> p 14 a
      ElaboratedDefinition a -> p 15 a
      ConstructorType a -> p 16 a
      KeyedNameSpan a -> p 17 a
      Occurrences a -> p 18 a
      LambdaLifted a -> p 19 a
      LambdaLiftedDefinition a -> p 20 a
      ClosureConverted a -> p 21 a
      ClosureConvertedType a -> p 22 a
      ClosureConvertedConstructorType a -> p 23 a
      -- Don't forget to add a case above!
    where
      p :: Persist a => Word8 -> a -> Put ()
      p tag a = do
        put tag
        put a

instance (forall a. Persist a => Persist (f a)) => PersistTag Query f where
  putTagged query =
    case query of
      InputFiles {} -> put
      FileText {} -> put
      ModuleFile q -> putTagged q
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
      InputFiles {} -> get
      FileText {} -> get
      ModuleFile q -> getTagged q
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
