{-# language OverloadedStrings #-}
module UTF16 where

import Protolude

import qualified Data.Char as Char
import qualified Language.Haskell.TH.Lib as TH
import Language.Haskell.TH.Quote
import qualified Data.Text.Internal.Encoding.Utf16 as Utf16

unit1 :: QuasiQuoter
unit1 = QuasiQuoter
  { quoteExp = \s ->
    case s of
      [c]
        | word16 <- fromIntegral $ Char.ord c
        , Utf16.validate1 word16
        -> TH.litE $ TH.integerL $ fromIntegral word16

      _ ->
        panic "UTF16.unit1 needs a single char"
  , quotePat = \s ->
    case s of
      [c]
        | word16 <- fromIntegral $ Char.ord c
        , Utf16.validate1 word16
        -> TH.litP $ TH.integerL $ fromIntegral word16

      _ ->
        panic "UTF16.unit1 needs a single char"
  , quoteType = panic "UTF16.unit1 quoteType"
  , quoteDec = panic "UTF16.unit1 quoteDec"
  }
