{-# language PatternSynonyms #-}
{-# language GeneralizedNewtypeDeriving #-}
module Lexer2.Class where

import Data.Word
import Lexer2.State
import Protolude hiding (State)

newtype Class = Class { unclass :: Word8 }
  deriving Show

newtype PremultipliedClass = PremultipliedClass { unpremultipliedClass :: Word8 }
  deriving Eq

{-# inline premultiply #-}
premultiply :: Class -> PremultipliedClass
premultiply (Class c) = PremultipliedClass $ unstate StateCount * c

{-# inline unpremultiply #-}
unpremultiply :: PremultipliedClass -> Class
unpremultiply (PremultipliedClass p) =
  Class $ p `div` unstate StateCount

newtype PremultipliedClassState = PremultipliedClassState { unpremultipliedClassState :: Word8 }

{-# inline premultipliedClassState #-}
premultipliedClassState :: PremultipliedClass -> State -> PremultipliedClassState
premultipliedClassState (PremultipliedClass c) (State s) = PremultipliedClassState $ c + s

{-# inline unpremultiplyClassState #-}
unpremultiplyClassState :: PremultipliedClassState -> (Class, State)
unpremultiplyClassState (PremultipliedClassState cs) =
  bimap Class State $ quotRem cs $ unstate StateCount

pattern WhitespaceClass :: Class
pattern WhitespaceClass = Class 0
pattern NewlineClass :: Class
pattern NewlineClass = Class 1
pattern AlphaClass :: Class
pattern AlphaClass = Class 2
pattern NumericClass :: Class
pattern NumericClass = Class 3
pattern LeftParenClass :: Class
pattern LeftParenClass = Class 4
pattern RightParenClass :: Class
pattern RightParenClass = Class 5
pattern DotClass :: Class
pattern DotClass = Class 6
pattern PrimeClass :: Class
pattern PrimeClass = Class 7
pattern MinusClass :: Class
pattern MinusClass = Class 8
pattern OperatorClass :: Class
pattern OperatorClass = Class 9
pattern LeftBraceClass :: Class
pattern LeftBraceClass = Class 10
pattern RightBraceClass :: Class
pattern RightBraceClass = Class 11
pattern EndOfFileClass :: Class
pattern EndOfFileClass = Class 12
pattern ErrorClass :: Class
pattern ErrorClass = Class 13
pattern ClassCount :: Class
pattern ClassCount = Class 14

