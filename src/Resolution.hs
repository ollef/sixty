{-# language BangPatterns #-}
module Resolution where

import Protolude

import qualified Data.HashMap.Lazy as HashMap

import Error (Error)
import qualified Error
import Name (Name)
import qualified Name
import qualified Presyntax
import Scope (Scopes)
import qualified Scope

moduleScopes
  :: Name.Module
  -> [(Name, Presyntax.Definition)]
  -> (Scopes, [Error])
moduleScopes module_ definitions =
  let
    (_, scopes, errs) =
      foldl' go mempty definitions
  in
  (scopes, reverse errs)
  where
    duplicate key name =
      Error.DuplicateName
        (Scope.KeyedName key (Name.Qualified module_ name))

    go (!scope, !scopes, !errs) (name, def) =
      case def of
        Presyntax.TypeDeclaration {} ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Scope.Type scope
              , HashMap.insert (name, Scope.Type) scope scopes
              , errs
              )

            Just key ->
              ( scope
              , scopes
              , duplicate key name : errs
              )

        Presyntax.ConstantDefinition {} ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Scope.Definition scope
              , HashMap.insert (name, Scope.Definition) scope scopes
              , errs
              )

            Just Scope.Type ->
              ( HashMap.insert name Scope.Definition scope
              , HashMap.insert (name, Scope.Definition) scope scopes
              , errs
              )

            Just Scope.Definition ->
              ( scope
              , scopes
              , duplicate Scope.Definition name : errs
              )

        Presyntax.DataDefinition {} ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Scope.Definition scope
              , HashMap.insert (name, Scope.Definition) scope scopes
              , errs
              )

            Just Scope.Type ->
              ( HashMap.insert name Scope.Definition scope
              , HashMap.insert (name, Scope.Definition) scope scopes
              , errs
              )

            Just Scope.Definition ->
              ( scope
              , scopes
              , duplicate Scope.Definition name : errs
              )
