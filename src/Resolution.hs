{-# language BangPatterns #-}
{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Resolution where

import Protolude

import qualified Data.HashMap.Lazy as HashMap

import Error (Error)
import qualified Error
import qualified Name
import qualified Presyntax
import Scope (Scopes)
import qualified Scope

moduleScopes
  :: Name.Module
  -> [Presyntax.Definition]
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

    go (!scope, !scopes, !errs) def =
      case def of
        Presyntax.TypeDeclaration name _ ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Scope.Type scope
              , HashMap.insert (name, Scope.Type) scope scopes
              , errs
              )

            Just Scope.Type ->
              ( scope
              , scopes
              , duplicate Scope.Type name : errs
              )

            Just Scope.Definition ->
              ( scope
              , HashMap.insert (name, Scope.Type) scope scopes
              , duplicate Scope.Type name : errs
              )

        Presyntax.ConstantDefinition name _ ->
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
