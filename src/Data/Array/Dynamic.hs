{-# language MagicHash #-}
module Data.Array.Dynamic where

import Protolude

import qualified Data.Primitive as Primitive

import GHC.Exts

data Array a = Array a !(Primitive.MutVar RealWorld (Primitive.MutableArray RealWorld a))

new :: Int -> a -> IO (Array a)
new size default_ = do
  array <- Primitive.newArray size default_
  var <- Primitive.newMutVar array
  pure $ Array default_ var

get :: Array a -> Int -> IO a
get (Array default_ var) i = do
  array <- Primitive.readMutVar var
  if i < Primitive.sizeofMutableArray array then
    Primitive.readArray array i
  else
    pure default_

set :: Array a -> Int -> a -> IO ()
set (Array default_ var) i value = do
  array <- Primitive.readMutVar var
  let
    size =
      Primitive.sizeofMutableArray array
  if i < size then do
    Primitive.writeArray array i value
  else do
    newArray <- Primitive.newArray (nextPowerOfTwo i) default_
    Primitive.copyMutableArray newArray 0 array 0 size
    Primitive.writeArray newArray i value
    Primitive.writeMutVar var newArray

nextPowerOfTwo :: Int -> Int
nextPowerOfTwo i =
  shiftL 1 $ finiteBitSize i - countLeadingZeros i
