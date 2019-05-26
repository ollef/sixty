{-# language GADTs #-}
{-# language TemplateHaskell #-}
module Query where

import Protolude

import Data.GADT.Compare.TH
import Data.HashMap.Lazy (HashMap)
import Rock.HashTag

import Name (Name)
import qualified Name
import qualified Presyntax
import qualified Resolution
import qualified Syntax

data Query a where
  ReadFile :: FilePath -> Query Text
  ParsedModule :: Name.Module -> Query [Presyntax.Definition]
  ParsedModuleMap :: Name.Module -> Query (HashMap (Name, Resolution.Key) Presyntax.Term)
  ParsedDefinition :: Resolution.KeyedName -> Query (Maybe Presyntax.Term)
  Scopes :: Name.Module -> Query Resolution.Scopes
  Visibility :: Resolution.KeyedName -> Presyntax.Name -> Query (Maybe Resolution.Visibility)
  ResolvedName :: Resolution.KeyedName -> Presyntax.Name -> Query (Maybe Name.Qualified)
  ElaboratedType :: Name.Qualified -> Query (Syntax.Type Void, Syntax.MetaSolutions)
  ElaboratedDefinition :: Name.Qualified -> Query (Maybe (Syntax.Term Void, Syntax.Type Void, Syntax.MetaSolutions))

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
