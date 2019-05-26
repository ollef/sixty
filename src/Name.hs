{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Name where

import Protolude

import Data.String
import qualified Meta
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc

import Orphans ()

newtype Name = Name Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, IsString)

newtype Module = Module Text
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, IsString)

data Qualified = Qualified !Module !Name
  deriving (Eq, Ord, Show, Generic, Hashable)

data Elaborated
  = Elaborated !Qualified
  -- TODO: Perhaps use resolution key for fine-grained meta origin tracking?
  | Meta !Qualified !Meta.Index
  deriving (Eq, Ord, Show, Generic, Hashable)

-------------------------------------------------------------------------------

instance IsString Qualified where
  fromString s =
    let
      t =
        fromString s

      (moduleDot, name) =
        Text.breakOnEnd "." t
    in
    case Text.stripSuffix "." moduleDot of
      Nothing ->
        Qualified (Module mempty) (Name t)

      Just module_ ->
        Qualified (Module module_) (Name name)

instance IsString Elaborated where
  fromString =
    Elaborated . fromString

instance Pretty Name where
  pretty (Name t) =
    pretty t

instance Pretty Module where
  pretty (Module t) =
    pretty t

instance Pretty Qualified where
  pretty (Qualified (Module module_) name)
    | Text.null module_ =
      pretty name
    | otherwise =
      pretty module_ <> "." <> pretty name

instance Pretty Elaborated where
  pretty elaboratedName =
    case elaboratedName of
      Elaborated qualifiedName ->
        pretty qualifiedName
      Meta qualifiedName (Meta.Index meta) ->
        pretty qualifiedName <> ".?" <> pretty meta
