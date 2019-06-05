{-# language GADTs #-}
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
  ParsedModule :: Name.Module -> Query [(Position.Absolute, Presyntax.Definition)]
  ParsedModuleMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Presyntax.Term)
  ModulePositionMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Position.Absolute)
  ParsedDefinition :: Scope.KeyedName -> Query (Maybe Presyntax.Term)
  Scopes :: Name.Module -> Query Scope.Scopes
  Visibility :: Scope.KeyedName -> Presyntax.Name -> Query (Maybe Scope.Visibility)
  ResolvedName :: Scope.KeyedName -> Presyntax.Name -> Query (Maybe Name.Qualified)
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Term Void, Syntax.Type Void))
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
      ErrorSpan {} -> hash
      KeyedNameSpan {} -> hash
