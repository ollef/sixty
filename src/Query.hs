{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language QuantifiedConstraints #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Query where

import Protolude hiding (IntMap)

import Data.Dependent.Sum
import Data.GADT.Compare.TH
import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import Data.IntMap (IntMap)
import Rock

import qualified ClosureConverted.Syntax as ClosureConverted
import qualified LambdaLifted.Syntax as LambdaLifted
import qualified Meta
import qualified Module
import Name (Name)
import qualified Name
import qualified Occurrences.Intervals as Occurrences
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
      ElaboratedType {} -> (==)
      ElaboratedDefinition {} -> (==)
      ElaboratingDefinition {} -> (==)
      ConstructorType {} -> (==)
      KeyedNameSpan {} -> (==)
      Occurrences {} -> (==)
      LambdaLifted {} -> (==)
      LambdaLiftedDefinition {} -> (==)
      ClosureConverted {} -> (==)
      ClosureConvertedType {} -> (==)
      ClosureConvertedConstructorType {} -> (==)
