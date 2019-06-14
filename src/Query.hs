{-# language GADTs #-}
{-# language OverloadedStrings #-}
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

data Query a where
  ReadFile :: FilePath -> Query Text
  ParsedModule :: Name.Module -> Query [(Position.Absolute, (Name, Presyntax.Definition))]
  ParsedModuleMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Presyntax.Definition)
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ParsedDefinition :: Scope.KeyedName -> Query (Maybe Presyntax.Definition)
  Scopes :: Name.Module -> Query Scope.Scopes
  Visibility :: Scope.KeyedName -> Name.Pre -> Query (Maybe Scope.Visibility)
  ResolvedName :: Scope.KeyedName -> Name.Pre -> Query (Maybe Name.Qualified)
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Definition, Syntax.Type Void))
  ConstructorType :: Name.QualifiedConstructor -> Query (Syntax.Type Void)
  ErrorSpan :: Error -> Query (FilePath, Span.Absolute)
  KeyedNameSpan :: Scope.KeyedName -> Query (FilePath, Span.Absolute)

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
      Visibility {} -> hash
      ResolvedName {} -> hash
      ElaboratedType {} -> hash
      ElaboratedDefinition {} -> hash
      ConstructorType {} -> hash
      ErrorSpan {} -> hash
      KeyedNameSpan {} -> hash

-- TODO
moduleFilePath :: Name.Module -> FilePath
moduleFilePath (Name.Module module_) =
  toS $ module_ <> ".lx"
