{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Name where

import Data.Persist
import Data.String
import qualified Data.Text as Text
import Extra
import Prettyprinter
import Protolude hiding (Constructor)

newtype Surface = Surface Text
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

unqualifyConstructor :: QualifiedConstructor -> Constructor
unqualifyConstructor (QualifiedConstructor _ c) = c

-------------------------------------------------------------------------------

instance IsString Qualified where
  fromString s =
    let t =
          fromString s

        (moduleDot, name) =
          Text.breakOnEnd "." t
     in case Text.stripSuffix "." moduleDot of
          Nothing ->
            Qualified (Module mempty) (Name t)
          Just module_ ->
            Qualified (Module module_) (Name name)

instance Pretty Surface where
  pretty (Surface t) =
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

instance Pretty Lifted where
  pretty (Lifted name 0) =
    pretty name
  pretty (Lifted name n) =
    pretty name <> "$" <> pretty n

instance Hashable Lifted where
  hashWithSalt =
    defaultHashWithSalt

  hash (Lifted m n) =
    hash m `hashWithSalt` n
