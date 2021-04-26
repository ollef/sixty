{-# LANGUAGE OverloadedStrings #-}

module Data.IntSeq.Properties where

import Data.IntSeq (IntSeq)
import qualified Data.IntSeq as IntSeq
import qualified Data.List as List
import Data.Tsil (Tsil)
import GHC.Exts (fromList)
import Hedgehog (Gen, forAll, (===))
import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Protolude hiding (list)

properties :: [(Hedgehog.PropertyName, Hedgehog.Property)]
properties =
  [
    ( "<>"
    , property $ do
        xs <- forAll genTsil
        ys <- forAll genTsil
        IntSeq.fromTsil xs <> IntSeq.fromTsil ys === IntSeq.fromTsil (xs <> ys)
    )
  ,
    ( "unsnoc/snoc"
    , property $ do
        xs <- forAll genIntSeq
        x <- forAll genInt
        IntSeq.unsnoc (IntSeq.snoc xs x) === Just (xs, x)
    )
  ,
    ( "length"
    , property $ do
        xs <- forAll genTsil
        IntSeq.length (IntSeq.fromTsil xs) === length xs
    )
  ,
    ( "member"
    , property $ do
        xs <- forAll genTsil
        x <- forAll genInt
        IntSeq.member x (IntSeq.fromTsil xs) === elem x xs
    )
  ,
    ( "elemIndex"
    , property $ do
        xs <- forAll genList
        x <- forAll genInt
        IntSeq.elemIndex x (IntSeq.fromList xs) === List.elemIndex x (reverse xs)
    )
  ,
    ( "index"
    , property $ do
        xs <- forAll genNonEmptyList
        i <- forAll $ Gen.int $ Range.constant 0 $ length xs - 1
        IntSeq.index (IntSeq.fromList xs) i === reverse xs List.!! i
    )
  ,
    ( "insertAt"
    , property $ do
        xs <- forAll genList
        x <- forAll genInt
        i <- forAll $ Gen.int $ Range.constant 0 $ length xs
        let list = reverse (drop i (reverse xs)) <> [x] <> reverse (take i (reverse xs))
        IntSeq.insertAt i x (IntSeq.fromList xs) === IntSeq.fromList list
    )
  ,
    ( "deleteFirst"
    , property $ do
        xs <- forAll genList
        x <- forAll genInt
        IntSeq.deleteFirst x (IntSeq.fromList xs) === IntSeq.fromList (reverse (reverse xs List.\\ [x]))
    )
  ,
    ( "fromList . toList == identity"
    , property $ do
        xs <- forAll genList
        IntSeq.toList (IntSeq.fromList xs) === xs
    )
  ,
    ( "fromTsil . toTsil == identity"
    , property $ do
        xs <- forAll genTsil
        IntSeq.toTsil (IntSeq.fromTsil xs) === xs
    )
  ]

property :: Hedgehog.PropertyT IO () -> Hedgehog.Property
property = Hedgehog.withTests 1000 . Hedgehog.property

genList :: Gen [Int]
genList = Gen.list (Range.linear 0 100) genInt

genNonEmptyList :: Gen [Int]
genNonEmptyList = Gen.list (Range.linear 1 100) genInt

genTsil :: Gen (Tsil Int)
genTsil = fromList <$> genList

genIntSeq :: Gen (IntSeq Int)
genIntSeq = IntSeq.fromTsil <$> genTsil

genInt :: Gen Int
genInt = Gen.int $ Range.linearFrom 0 (-100) 100
