{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module UTF8 where

import qualified Data.Char as Char
import qualified Data.Text.Internal.Encoding.Utf8 as Utf8
import qualified Language.Haskell.TH.Lib as TH
import Language.Haskell.TH.Quote
import Protolude

unit1 :: QuasiQuoter
unit1 =
  QuasiQuoter
    { quoteExp = \case
        [c]
          | word8 <- fromIntegral $ Char.ord c
          , Utf8.validate1 word8 ->
              TH.litE $ TH.integerL $ fromIntegral word8
        _ ->
          panic "UTF8.unit1 needs a single char"
    , quotePat = \case
        [c]
          | word8 <- fromIntegral $ Char.ord c
          , Utf8.validate1 word8 ->
              TH.litP $ TH.integerL $ fromIntegral word8
        _ ->
          panic "UTF8.unit1 needs a single char"
    , quoteType = panic "UTF8.unit1 quoteType"
    , quoteDec = panic "UTF8.unit1 quoteDec"
    }
