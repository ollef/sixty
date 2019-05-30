{-# language BangPatterns #-}
{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Resolution where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Error (Error)
import qualified Error
import Name (Name)
import qualified Name
import qualified Presyntax

data Key
  = TypeDeclaration
  | ConstantDefinition
  deriving (Eq, Ord, Show, Generic, Hashable)

data KeyedName = KeyedName !Name.Qualified !Key
  deriving (Eq, Ord, Show, Generic, Hashable)

unkeyed :: KeyedName -> Name.Qualified
unkeyed (KeyedName name _) = name

data Visibility
  = Type
  | Definition
  deriving (Eq, Show, Generic, Hashable)

type Scope =
  HashMap Name Visibility

type Scopes =
  HashMap (Name, Key) Scope

moduleScopes
  :: [Presyntax.Definition]
  -> (Scopes, [Error])
moduleScopes definitions =
  let
    (_, scopes, errs) =
      foldl' go mempty definitions
  in
  (scopes, reverse errs)
  where
    go (!scope, !scopes, !errs) def =
      case def of
        Presyntax.TypeDeclaration name _ ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Type scope
              , HashMap.insert (name, TypeDeclaration) scope scopes
              , errs
              )

            Just Type ->
              ( scope
              , scopes
              , Error.DuplicateName name : errs
              )

            Just Definition ->
              ( scope
              , HashMap.insert (name, TypeDeclaration) scope scopes
              , Error.DuplicateName name : errs
              )

        Presyntax.ConstantDefinition name _ ->
          case HashMap.lookup name scope of
            Nothing ->
              ( HashMap.insert name Definition scope
              , HashMap.insert (name, ConstantDefinition) scope scopes
              , errs
              )

            Just Type ->
              ( HashMap.insert name Definition scope
              , HashMap.insert (name, ConstantDefinition) scope scopes
              , errs
              )

            Just Definition ->
              ( scope
              , scopes
              , Error.DuplicateName name : errs
              )

keyed :: Presyntax.Definition -> ((Name, Key), Presyntax.Term)
keyed def =
  case def of
    Presyntax.ConstantDefinition name term ->
      ((name, ConstantDefinition), term)

    Presyntax.TypeDeclaration name type_ ->
      ((name, TypeDeclaration), type_)