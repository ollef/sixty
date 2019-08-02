{-# language BangPatterns #-}
{-# language OverloadedStrings #-}
module Resolution where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet

import Error (Error)
import qualified Error
import Name (Name(Name))
import qualified Name
import qualified Presyntax
import Scope (Scope)
import qualified Module
import qualified Scope

moduleScopes
  :: Name.Module
  -> [(Name, Presyntax.Definition)]
  -> (((Scope, Scope.Visibility), Scope.Module), [Error])
moduleScopes module_ definitions =
  let
    (finalScope, finalVisibility, scopes, errs) =
      foldl' go (mempty, mempty, mempty, mempty) definitions
  in
  (((finalScope, finalVisibility), scopes), reverse errs)
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
          let
            ok =
              ( HashMap.insertWith (<>) prename (Scope.Name qualifiedName) scope
              , HashMap.insertWith max qualifiedName Scope.Definition visibility
              , HashMap.insert (name, Scope.Definition) (scope, visibility) scopes
              , errs
              )
          in
          case HashMap.lookup qualifiedName visibility of
            Nothing ->
              ok

            Just Scope.Type ->
              ok

            Just Scope.Definition ->
              ( scope
              , visibility
              , scopes
              , duplicate Scope.Definition qualifiedName : errs
              )
      in
      case def of
        Presyntax.TypeDeclaration {} ->
          case HashMap.lookup qualifiedName visibility of
            Just _ ->
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

        Presyntax.DataDefinition _ constrTypes ->
          let
            (scope', visibility', scopes', errs') =
              definitionCase

            constrs =
              HashMap.fromListWith (<>)
              [ ( Name.Pre text
                , Scope.Constructors $
                  HashSet.singleton $
                  Name.QualifiedConstructor qualifiedName constr
                )
              | (cs, _) <- constrTypes
              , constr@(Name.Constructor text) <- cs
              ]

          in
          (HashMap.unionWith (<>) constrs scope', visibility', scopes', errs')

-- TODO: Error for names that aren't exposed
exposedNames :: Module.ExposedNames -> HashMap Name.Pre a -> HashMap Name.Pre a
exposedNames exposed m =
  case exposed of
    Module.AllExposed ->
      m

    Module.Exposed names ->
      HashMap.intersection m (HashSet.toMap names)

importedNames :: Semigroup a => Module.Import -> HashMap Name.Pre a -> HashMap Name.Pre a
importedNames import_ m =
  HashMap.unionWith (<>) unqualifiedNames qualifiedNames
  where
    unqualifiedNames =
      exposedNames (Module._importedNames import_) m

    qualifiedNames =
      HashMap.fromList
        [ (Module._alias import_ <> "." <> prename, a)
        | (prename, a) <- HashMap.toList m
        ]
