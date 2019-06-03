{-# language GADTs #-}
{-# language TemplateHaskell #-}
module Query where

import Protolude

import Data.GADT.Compare.TH
import Data.HashMap.Lazy (HashMap)
import Rock.HashTag

import Name (Name)
import qualified Name
import qualified Position
import qualified Presyntax
import qualified Scope
import qualified Syntax

data Query a where
  ReadFile :: FilePath -> Query Text
  ParsedModule :: Name.Module -> Query [(Position.Absolute, Presyntax.Definition)]
  ParsedModuleMap :: Name.Module -> Query (HashMap (Scope.Key, Name) Presyntax.Term)
  ParsedDefinition :: Scope.KeyedName -> Query (Maybe Presyntax.Term)
  Scopes :: Name.Module -> Query Scope.Scopes
  Visibility :: Scope.KeyedName -> Presyntax.Name -> Query (Maybe Scope.Visibility)
  ResolvedName :: Scope.KeyedName -> Presyntax.Name -> Query (Maybe Name.Qualified)
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Term Void, Syntax.Type Void))

deriveGEq ''Query
deriveGCompare ''Query

instance HashTag Query where
  hashTagged query =
    case query of
      ReadFile {} -> hash
      ParsedModule {} -> hash
      ParsedModuleMap {} -> hash
      ParsedDefinition {} -> hash
      Scopes {} -> hash
      Visibility {} -> hash
      ResolvedName {} -> hash
      ElaboratedType {} -> hash
      ElaboratedDefinition {} -> hash
