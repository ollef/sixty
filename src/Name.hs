{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Name where

import Protolude hiding (Constructor)

import qualified Data.ByteString as ByteString
import Data.Persist
import Data.String
import Data.Text.Prettyprint.Doc

import Extra

newtype Surface = Surface ByteString
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Semigroup, Hashable, Persist)

newtype Name = Name ByteString
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Hashable, Persist)

newtype Constructor = Constructor ByteString
  deriving stock (Eq, Ord, Show)
  deriving newtype (IsString, Hashable, Persist)

newtype Module = Module ByteString
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
    let
      t =
        fromString s

      (moduleDot, name) =
        ByteString.breakEnd (== fromIntegral (ord '.')) t
    in
    case ByteString.stripSuffix "." moduleDot of
      Nothing ->
        Qualified (Module mempty) (Name t)

      Just module_ ->
        Qualified (Module module_) (Name name)

instance Pretty Surface where
  pretty (Surface t) =
    pretty $ decodeUtf8 t

instance Pretty Name where
  pretty (Name t) =
    pretty $ decodeUtf8 t

instance Pretty Constructor where
  pretty (Constructor c) =
    pretty $ decodeUtf8 c

instance Pretty Module where
  pretty (Module t) =
    pretty $ decodeUtf8 t

instance Pretty Qualified where
  pretty (Qualified (Module module_) name)
    | ByteString.null module_ =
      pretty name
    | otherwise =
      pretty (decodeUtf8 module_) <> "." <> pretty name

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
