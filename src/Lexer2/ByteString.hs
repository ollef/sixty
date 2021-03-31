module Lexer2.ByteString where

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString.Builder.Extra as Builder
import qualified Data.ByteString.Internal as ByteString
import qualified Data.ByteString.Lazy as Lazy
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Protolude

generateWord8 :: Int -> (Int -> Word8) -> ByteString
generateWord8 size f = ByteString.pack $ map f [0..size - 1]

generateInt8 :: Int -> (Int -> Int8) -> ByteString
generateInt8 size f =
  Lazy.toStrict $ Builder.toLazyByteString $ mconcat $ map (Builder.int8 . f) [0..size - 1]

generateWord16 :: Int -> (Int -> Word16) -> ByteString
generateWord16 size f =
  Lazy.toStrict $ Builder.toLazyByteString $ mconcat $ map (Builder.word16Host . f) [0..size - 1]

bytesFromByteString :: ByteString -> Bytes
bytesFromByteString (ByteString.PS fp offset size) =
  mkBytes fp (fromIntegral offset) (fromIntegral size)
