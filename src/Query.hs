{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Query where

import Protolude

import Data.GADT.Compare.TH
import Data.HashMap.Lazy (HashMap)
import Rock.HashTag

import Error (Error)
import Name (Name)
import qualified Name
import qualified Position
import qualified Presyntax
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)

data Query a where
  ReadFile :: FilePath -> Query Text
  ParsedModule :: Name.Module -> Query [(Position.Absolute, (Name, Presyntax.Definition))]
  ParsedModuleMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Presyntax.Definition)
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ParsedDefinition :: Scope.KeyedName -> Query (Maybe Presyntax.Definition)
  Scopes :: Name.Module -> Query Scope.Module
  ResolvedName :: Scope.KeyedName -> Name.Pre -> Query (Maybe Scope.Entry)
  Visibility :: Scope.KeyedName -> Name.Qualified -> Query Scope.Key
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void))
  ConstructorType :: Name.QualifiedConstructor -> Query (Telescope Syntax.Type Syntax.Type Void)
  ErrorSpan :: Error -> Query (FilePath, Span.Absolute)
  KeyedNameSpan :: Scope.KeyedName -> Query (FilePath, Span.Absolute)

deriving instance Show (Query a)

deriveGEq ''Query
deriveGCompare ''Query

instance HashTag Query where
  hashTagged query =
    case query of
      ReadFile {} -> hash
      ParsedModule {} -> hash
      ParsedModuleMap {} -> hash
      ModulePositionMap {} -> hash
      ParsedDefinition {} -> hash
      Scopes {} -> hash
      ResolvedName {} -> hash
      Visibility {} -> hash
      ElaboratedType {} -> hash
      ElaboratedDefinition {} -> hash
      ConstructorType {} -> hash
      ErrorSpan {} -> hash
      KeyedNameSpan {} -> hash

-- TODO
moduleFilePath :: Name.Module -> FilePath
moduleFilePath (Name.Module module_) =
  toS $ module_ <> ".lx"
