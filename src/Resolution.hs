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
  -> (((Scope, Scope, Scope.Visibility), Scope.Module), [Error])
moduleScopes module_@(Name.Module moduleText) definitions =
  let
    (finalPrivateScope, finalPublicScope, finalVisibility, scopes, errs) =
      foldl' go mempty definitions
  in
  (((finalPrivateScope, finalPublicScope, finalVisibility), scopes), reverse errs)
  where
    duplicate key qualifiedName =
      Error.DuplicateName
        (Scope.KeyedName key qualifiedName)

    go (!privateScope, !publicScope, !visibility, !scopes, !errs) (name@(Name nameText), def) =
      let
        prename =
          Name.Pre nameText

        qualifiedPreName =
          Name.Pre $ moduleText <> "." <> nameText

        qualifiedName =
          Name.Qualified module_ name

        privateScope' =
          HashMap.insertWith (<>) qualifiedPreName (Scope.Name qualifiedName) $
          HashMap.insertWith (<>) prename (Scope.Name qualifiedName) privateScope

        publicScope' =
          HashMap.insertWith (<>) prename (Scope.Name qualifiedName) publicScope

        definitionCase =
          let
            ok =
              ( privateScope'
              , publicScope'
              , HashMap.insertWith max qualifiedName Scope.Definition visibility
              , HashMap.insert (name, Scope.Definition) (privateScope, visibility) scopes
              , errs
              )
          in
          case HashMap.lookup qualifiedName visibility of
            Nothing ->
              ok

            Just Scope.Type ->
              ok

            Just Scope.Definition ->
              ( privateScope
              , publicScope
              , visibility
              , scopes
              , duplicate Scope.Definition qualifiedName : errs
              )
      in
      case def of
        Presyntax.TypeDeclaration {} ->
          case HashMap.lookup qualifiedName visibility of
            Just key ->
              ( privateScope
              , publicScope
              , visibility
              , scopes
              , duplicate key qualifiedName : errs
              )

            Nothing ->
              ( privateScope'
              , publicScope'
              , HashMap.insertWith max qualifiedName Scope.Type visibility
              , HashMap.insert (name, Scope.Type) (privateScope, visibility) scopes
              , errs
              )

        Presyntax.ConstantDefinition {} ->
          definitionCase

        Presyntax.DataDefinition _ _ constrDefs ->
          let
            (privateScope'', publicScope'', visibility', scopes', errs') =
              definitionCase

            constructors =
              [ ( ( Name.Pre text
                  , Scope.Constructors $
                    HashSet.singleton $
                    Name.QualifiedConstructor qualifiedName constr
                  )
                , ( Name.Pre $ moduleText <> "." <> text
                  , Scope.Constructors $
                    HashSet.singleton $
                    Name.QualifiedConstructor qualifiedName constr
                  )
                )
              | constrDef <- constrDefs
              , let
                  constrs =
                    case constrDef of
                      Presyntax.GADTConstructors cs _ ->
                        snd <$> cs

                      Presyntax.ADTConstructor _ c _ ->
                        [c]
              , constr@(Name.Constructor text) <- constrs
              ]

            publicConstructors =
              HashMap.fromListWith (<>) $ fst <$> constructors

            privateConstructors =
              HashMap.fromListWith (<>) $ concatMap (\(a, b) -> [a, b]) constructors

          in
          ( HashMap.unionWith (<>) privateConstructors privateScope''
          , HashMap.unionWith (<>) publicConstructors publicScope''
          , visibility'
          , scopes'
          , errs'
          )

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
