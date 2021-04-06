{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Resolution where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Error (Error)
import qualified Error
import qualified Module
import Name (Name (Name))
import qualified Name
import qualified Position
import Protolude
import Scope (Scope)
import qualified Scope
import qualified Span
import qualified Surface.Syntax as Surface

moduleScopes ::
  Name.Module ->
  [(Position.Absolute, (Name, Surface.Definition))] ->
  (((Scope, Scope, Scope.Visibility), Scope.Module), [Error])
moduleScopes module_@(Name.Module moduleText) definitions =
  let (finalPrivateScope, finalPublicScope, finalVisibility, scopes, errs) =
        foldl' go mempty definitions
   in (((finalPrivateScope, finalPublicScope, finalVisibility), scopes), reverse errs)
  where
    duplicate key qualifiedName =
      Error.DuplicateName (Scope.KeyedName key qualifiedName)

    go (!privateScope, !publicScope, !visibility, !scopes, !errs) (position, (name@(Name nameText), def)) =
      let span
            | s : _ <- Surface.spans def =
              Span.absoluteFrom position s
            | otherwise =
              Span.Absolute position position

          surfaceName =
            Name.Surface nameText

          qualifiedSurfaceName =
            Name.Surface $ moduleText <> "." <> nameText

          qualifiedName =
            Name.Qualified module_ name

          privateScope' =
            HashMap.insertWith (<>) qualifiedSurfaceName (Scope.Name qualifiedName) $
              HashMap.insertWith (<>) surfaceName (Scope.Name qualifiedName) privateScope

          publicScope' =
            HashMap.insertWith (<>) surfaceName (Scope.Name qualifiedName) publicScope

          definitionCase =
            let ok =
                  ( privateScope'
                  , publicScope'
                  , HashMap.insertWith max qualifiedName Scope.Definition visibility
                  , HashMap.insert (name, Scope.Definition) (privateScope, visibility) scopes
                  , errs
                  )
             in case HashMap.lookup qualifiedName visibility of
                  Nothing ->
                    ok
                  Just Scope.Type ->
                    ok
                  Just Scope.Definition ->
                    ( privateScope
                    , publicScope
                    , visibility
                    , scopes
                    , duplicate Scope.Definition qualifiedName span : errs
                    )
       in case def of
            Surface.TypeDeclaration {} ->
              case HashMap.lookup qualifiedName visibility of
                Just key ->
                  ( privateScope
                  , publicScope
                  , visibility
                  , scopes
                  , duplicate key qualifiedName span : errs
                  )
                Nothing ->
                  ( privateScope'
                  , publicScope'
                  , HashMap.insertWith max qualifiedName Scope.Type visibility
                  , HashMap.insert (name, Scope.Type) (privateScope, visibility) scopes
                  , errs
                  )
            Surface.ConstantDefinition {} ->
              definitionCase
            Surface.DataDefinition _ _ _ constrDefs ->
              let (privateScope'', publicScope'', visibility', scopes', errs') =
                    definitionCase

                  constructors =
                    [ (
                        ( Name.Surface text
                        , Scope.Constructors
                            (HashSet.singleton $ Name.QualifiedConstructor qualifiedName constr)
                            mempty
                        )
                      ,
                        ( Name.Surface $ moduleText <> "." <> text
                        , Scope.Constructors
                            (HashSet.singleton $ Name.QualifiedConstructor qualifiedName constr)
                            mempty
                        )
                      )
                    | constrDef <- constrDefs
                    , let constrs =
                            case constrDef of
                              Surface.GADTConstructors cs _ ->
                                snd <$> cs
                              Surface.ADTConstructor _ c _ ->
                                [c]
                    , constr@(Name.Constructor text) <- constrs
                    ]

                  privateScope''' =
                    HashMap.insertWith (<>) qualifiedSurfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) $
                      HashMap.insertWith (<>) surfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) privateScope''

                  publicScope''' =
                    HashMap.insertWith (<>) surfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) publicScope''

                  publicConstructors =
                    HashMap.fromListWith (<>) $ fst <$> constructors

                  privateConstructors =
                    HashMap.fromListWith (<>) $ concatMap (\(a, b) -> [a, b]) constructors
               in ( HashMap.unionWith (<>) privateConstructors privateScope'''
                  , HashMap.unionWith (<>) publicConstructors publicScope'''
                  , visibility'
                  , scopes'
                  , errs'
                  )

-- TODO: Error for names that aren't exposed
exposedNames :: Module.ExposedNames -> HashMap Name.Surface a -> HashMap Name.Surface a
exposedNames exposed m =
  case exposed of
    Module.AllExposed ->
      m
    Module.Exposed names ->
      HashMap.intersection m (HashSet.toMap names)

importedNames :: Semigroup a => Module.Import -> HashMap Name.Surface a -> HashMap Name.Surface a
importedNames import_ m =
  HashMap.unionWith (<>) unqualifiedNames qualifiedNames
  where
    unqualifiedNames =
      exposedNames (Module._importedNames import_) m

    qualifiedNames =
      HashMap.fromList
        [ (snd (Module._alias import_) <> "." <> surfaceName, a)
        | (surfaceName, a) <- HashMap.toList m
        ]
