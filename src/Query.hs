{-# language GADTs #-}
{-# language TemplateHaskell #-}
module Query where

import Protolude

import Data.GADT.Compare.TH
import Rock.HashTag
import Data.HashMap.Lazy (HashMap)

import qualified Name
import qualified Presyntax
import qualified Resolution
import qualified Syntax

data Query a where
  ReadFile :: FilePath -> Query Text
  ParsedModule :: Name.Module -> Query [Presyntax.Definition]
  ParsedModuleMap :: Name.Module -> Query (HashMap Resolution.Key Presyntax.Term)
  ParsedDefinition :: Name.Module -> Resolution.Key -> Query (Maybe Presyntax.Term)
  Scopes :: Name.Module -> Query Resolution.Scopes
  Visibility :: Name.Module -> Resolution.Key -> Presyntax.Name -> Query (Maybe Resolution.Visibility)
  ResolvedName :: Name.Module -> Resolution.Key -> Presyntax.Name -> Query (Maybe Name.Qualified)
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
