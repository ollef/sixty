{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Name where

import Protolude hiding (Constructor)

import Data.String
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Persist

import Extra

newtype Pre = Pre Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Semigroup, Hashable, Persist)

newtype Name = Name Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Hashable, Persist)

newtype Constructor = Constructor Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Hashable, Persist)

newtype Module = Module Text
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Hashable, Persist)

data Qualified = Qualified !Module !Name
  deriving (Eq, Ord, Show, Generic, Persist)

data QualifiedConstructor = QualifiedConstructor !Qualified !Constructor
  deriving (Eq, Ord, Show, Generic, Persist)

data Lifted = Lifted !Qualified !Int
  deriving (Eq, Ord, Show, Generic, Persist)

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

instance Pretty Pre where
  pretty (Pre t) =
    pretty t

instance Pretty Name where
  pretty (Name t) =
    pretty t

instance Pretty Constructor where
  pretty (Constructor c) =
    pretty c

instance Pretty Module where
  pretty (Module t) =
    pretty t

instance Pretty Qualified where
  pretty (Qualified (Module module_) name)
    | Text.null module_ =
      pretty name
    | otherwise =
      pretty module_ <> "." <> pretty name

instance Hashable Qualified where
  hashWithSalt =
    defaultHashWithSalt

  hash (Qualified m n) =
    hash m `hashWithSalt` n

instance Pretty QualifiedConstructor where
  pretty (QualifiedConstructor n c) =
    pretty n <> "." <> pretty c

instance Hashable QualifiedConstructor where
  hashWithSalt =
    defaultHashWithSalt

  hash (QualifiedConstructor m n) =
    hash m `hashWithSalt` n

instance Hashable Lifted where
  hashWithSalt =
    defaultHashWithSalt

  hash (Lifted m n) =
    hash m `hashWithSalt` n
