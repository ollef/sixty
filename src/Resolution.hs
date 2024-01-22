{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}
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

moduleScopes
  :: Name.Module
  -> [(Position.Absolute, (Name, Surface.Definition))]
  -> ((Scope, Scope), [Error])
moduleScopes module_@(Name.Module moduleText) definitions =
  let (finalPrivateScope, finalPublicScope, _seen, errs) =
        foldl' go mempty definitions
   in ((finalPrivateScope, finalPublicScope), reverse errs)
  where
    go (!privateScope, !publicScope, !seen, !errs) (position, (name@(Name nameText), def)) =
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

          entity entityType
            | HashSet.member (entityType, qualifiedName) seen =
                ( privateScope
                , publicScope
                , seen
                , Error.DuplicateName entityType qualifiedName span : errs
                )
            | otherwise =
                let privateScope' =
                      HashMap.insertWith (<>) qualifiedSurfaceName (Scope.Name qualifiedName) $
                        HashMap.insertWith (<>) surfaceName (Scope.Name qualifiedName) privateScope

                    publicScope' =
                      HashMap.insertWith (<>) surfaceName (Scope.Name qualifiedName) publicScope
                 in ( privateScope'
                    , publicScope'
                    , HashSet.insert (entityType, qualifiedName) seen
                    , errs
                    )
       in case def of
            Surface.TypeDeclaration {} ->
              entity Scope.Type
            Surface.ConstantDefinition {} ->
              entity Scope.Definition
            Surface.DataDefinition _ _ _ constrDefs ->
              let (privateScope', publicScope', seen', errs') =
                    entity Scope.Definition

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

                  privateScope'' =
                    HashMap.insertWith (<>) qualifiedSurfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) $
                      HashMap.insertWith (<>) surfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) privateScope'

                  publicScope'' =
                    HashMap.insertWith (<>) surfaceName (Scope.Constructors mempty $ HashSet.singleton qualifiedName) publicScope'

                  publicConstructors =
                    HashMap.fromListWith (<>) $ fst <$> constructors

                  privateConstructors =
                    HashMap.fromListWith (<>) $ concatMap (\(a, b) -> [a, b]) constructors
               in ( HashMap.unionWith (<>) privateConstructors privateScope''
                  , HashMap.unionWith (<>) publicConstructors publicScope''
                  , seen'
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

importedNames :: (Semigroup a) => Module.Import -> HashMap Name.Surface a -> HashMap Name.Surface a
importedNames import_ m =
  HashMap.unionWith (<>) unqualifiedNames qualifiedNames
  where
    unqualifiedNames =
      exposedNames import_.importedNames m

    qualifiedNames =
      HashMap.fromList
        [ (snd import_.alias <> "." <> surfaceName, a)
        | (surfaceName, a) <- HashMap.toList m
        ]
