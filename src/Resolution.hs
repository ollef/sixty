{-# language BangPatterns #-}
module Resolution where

import Protolude

import qualified Data.HashMap.Lazy as HashMap

import Error (Error)
import qualified Error
import Name (Name(Name))
import qualified Name
import qualified Presyntax
import qualified Scope

moduleScopes
  :: Name.Module
  -> [(Name, Presyntax.Definition)]
  -> (Scope.Module, [Error])
moduleScopes module_ definitions =
  let
    (_, _, scopes, errs) =
      foldl' go (mempty, mempty, mempty, mempty) definitions
  in
  (scopes, reverse errs)
  where
    duplicate key qualifiedName =
      Error.DuplicateName
        (Scope.KeyedName key qualifiedName)

    go (!scope, !visibility, !scopes, !errs) (name@(Name nameText), def) =
      let
        prename =
          Name.Pre nameText

        qualifiedName =
          Name.Qualified module_ name

        definitionCase =
          case HashMap.lookup prename scope of
            Just (Scope.Name qualifiedName')
              | qualifiedName == qualifiedName'
              , Scope.Definition <- visibility HashMap.! qualifiedName ->
                ( scope
                , visibility
                , scopes
                , duplicate Scope.Definition qualifiedName : errs
                )

            _ ->
              ( HashMap.insertWith (<>) prename (Scope.Name qualifiedName) scope
              , HashMap.insertWith max qualifiedName Scope.Definition visibility
              , HashMap.insert (name, Scope.Definition) (scope, visibility) scopes
              , errs
              )
      in
      case def of
        Presyntax.TypeDeclaration {} ->
          case HashMap.lookup prename scope of
            Just (Scope.Name qualifiedName')
              | qualifiedName == qualifiedName' ->
                ( scope
                , visibility
                , scopes
                , duplicate (visibility HashMap.! qualifiedName) qualifiedName : errs
                )

            _ ->
              ( HashMap.insertWith (<>) prename (Scope.Name qualifiedName) scope
              , HashMap.insertWith max qualifiedName Scope.Type visibility
              , HashMap.insert (name, Scope.Type) (scope, visibility) scopes
              , errs
              )

        Presyntax.ConstantDefinition {} ->
          definitionCase

        Presyntax.DataDefinition {} ->
          definitionCase
