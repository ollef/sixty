{-# language TemplateHaskell #-}
{-# language UnboxedTuples #-}
{-# language MagicHash #-}
{-# language OverloadedStrings #-}
module Lexer2.Classification where

import qualified Data.Char as Char
import GHC.Exts
import Instances.TH.Lift ()
import Language.Haskell.TH.Lib
import qualified Lexer2.ByteString as ByteString
import Lexer2.State
import qualified Lexer2.UTF8 as UTF8
import Protolude hiding (State, state, length, lift)

{-# inline classify #-}
classify :: Addr# -> (# PremultipliedClass, Int# #)
classify position = do
  let
    c1 = indexCharOffAddr# position 0#
  if UTF8.validate1 c1 then
    (# classify1 c1, 1# #)
  else do
    let
      c2 = indexCharOffAddr# position 1#
    if UTF8.validate2 c1 then
      (# classifyChar $ UTF8.chr2 c1 c2, 2# #)
    else do
      let
        c3 = indexCharOffAddr# position 2#
      if UTF8.validate3 c1 then
        (# classifyChar $ UTF8.chr3 c1 c2 c3, 3# #)
      else do
        let
          c4 = indexCharOffAddr# position 3#
        (# classifyChar $ UTF8.chr4 c1 c2 c3 c4, 4# #)

classify1 :: Char# -> PremultipliedClass
classify1 char =
  PremultipliedClass $
  fromIntegral $
  W#
  -- W16# -- Seems to cause worse optimisation for some reason
  (indexWord16OffAddr#
    $(litE $ bytesPrimL $ ByteString.bytesFromByteString $
      ByteString.generateWord16 128 $ \c -> premultipliedClassToWord16 $ premultiply $
        case c of
          0 -> EndOfFileClass
          _ ->
            case chr c of
              _ | ord 'a' <= c && c <= ord 'z' -> AlphaClass
              _ | ord 'A' <= c && c <= ord 'Z' -> AlphaClass
              '_' -> AlphaClass
              _ | ord '0' <= c && c <= ord '9' -> NumericClass
              '.' -> DotClass
              '\n' -> NewlineClass
              ' ' -> WhitespaceClass
              '\t' -> WhitespaceClass
              '-' -> MinusClass
              '\'' -> PrimeClass
              '!' -> OperatorClass
              '#' -> OperatorClass
              '$' -> OperatorClass
              '%' -> OperatorClass
              '&' -> OperatorClass
              '*' -> OperatorClass
              '+' -> OperatorClass
              ',' -> OperatorClass
              '/' -> OperatorClass
              ':' -> OperatorClass
              ';' -> OperatorClass
              '<' -> OperatorClass
              '=' -> OperatorClass
              '>' -> OperatorClass
              '?' -> OperatorClass
              '@' -> OperatorClass
              '\\' -> OperatorClass
              '^' -> OperatorClass
              '`' -> OperatorClass
              '|' -> OperatorClass
              '~' -> OperatorClass
              '(' -> LeftParenClass
              ')' -> RightParenClass
              '{' -> LeftBraceClass
              '}' -> RightBraceClass
              _ -> ErrorClass
    )
    (ord# char)
  )


classifyChar :: Char -> PremultipliedClass
classifyChar c
  | Char.isAlphaNum c = premultiply AlphaClass
  | Char.isSymbol c = premultiply OperatorClass
  | Char.isPunctuation c = premultiply OperatorClass
  | otherwise = premultiply ErrorClass
