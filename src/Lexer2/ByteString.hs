module Lexer2.ByteString where

import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Internal as ByteString
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Protolude

generate :: Int -> (Int -> Word8) -> ByteString
generate size f =
  snd $
  ByteString.mapAccumL (\i _ -> (i + 1, f i)) 0 $
  ByteString.replicate size 0

bytesFromByteString :: ByteString -> Bytes
bytesFromByteString (ByteString.PS fp offset size) =
  mkBytes fp (fromIntegral offset) (fromIntegral size)
