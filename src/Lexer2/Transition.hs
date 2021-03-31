{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
{-# language MagicHash #-}
{-# language OverloadedStrings #-}
module Lexer2.Transition where

import GHC.Exts
import Instances.TH.Lift ()
import Language.Haskell.TH.Lib
import qualified Lexer2.ByteString as ByteString
import Lexer2.State
import Protolude hiding (State, state, length, lift)

newlineMultiplier :: PremultipliedClass -> Int
newlineMultiplier (PremultipliedClass (fromIntegral -> (I# off))) =
  I#
  (indexInt8OffAddr#
    $(litE $ bytesPrimL $ ByteString.bytesFromByteString $
    ByteString.generateInt8 (fromIntegral $ premultipliedClassToWord16 $ premultiply ClassCount) $ \pc ->
      case unpremultiply $ PremultipliedClass $ fromIntegral pc of
        NewlineClass -> 1
        _ -> 0
     )
     off
  )

tokenLengthMultiplier :: State -> Int
tokenLengthMultiplier (State (fromIntegral -> I# off)) =
  I#
  (indexInt8OffAddr#
    $(litE $ bytesPrimL $ ByteString.bytesFromByteString $
      ByteString.generateInt8 (fromIntegral $ stateToWord8 StateCount) $ \s -> case State $ fromIntegral s of
        InitialState -> 0
        IdentifierState -> 1
        IdentifierDotState -> 1
        NumberState -> 1
        MinusState -> 1
        LeftParenState -> 1
        RightParenState -> 1
        LeftBraceState -> 1
        RightBraceState -> 1
        OperatorState -> 1
        SingleLineCommentState -> 0
        MultiLineCommentState -> 0
        MultiLineCommentMinusState -> 0
        ErrorState -> 1
        NumberDone -> 0
        IdentifierDone -> 0
        OperatorDone -> 0
        LeftParenDone -> 0
        RightParenDone -> 0
        ErrorDone -> 0
        EndOfFileDone -> 0
        _ -> panic $ " tokenLengthShouldIncreaseTable: no such state " <> show s
    )
    off
  )

doneFromOffset :: State -> Int#
doneFromOffset (State (fromIntegral -> I# off)) =
  indexInt8OffAddr#
    $(litE $ bytesPrimL $ ByteString.bytesFromByteString $
      ByteString.generateInt8 (fromIntegral $ stateToWord8 StateCount) $ \s -> case State $ fromIntegral s of
        IdentifierDotState -> -1
        _ -> 0
    )
    off

nextState :: PremultipliedClassState -> State
nextState (PremultipliedClassState (fromIntegral -> (I# off))) =
  State $
  fromIntegral $
  W#
  (indexWord8OffAddr#
    $(litE $ bytesPrimL $ ByteString.bytesFromByteString $
      ByteString.generateWord8 (fromIntegral (stateToWord8 StateCount) * fromIntegral (classToWord8 ClassCount)) $ \i -> do
        let
          (class_, state) =
            unpremultiplyClassState $ PremultipliedClassState $ fromIntegral i
        stateToWord8 $
          case state of
            InitialState ->
              case class_ of
                WhitespaceClass -> InitialState
                NewlineClass -> InitialState
                AlphaClass -> IdentifierState
                NumericClass -> NumberState
                LeftParenClass -> LeftParenState
                RightParenClass -> RightParenState
                DotClass -> OperatorState
                PrimeClass -> ErrorState -- TODO
                MinusClass -> MinusState
                LeftBraceClass -> LeftBraceState
                RightBraceClass -> RightBraceState
                OperatorClass -> OperatorState
                EndOfFileClass -> EndOfFileDone
                ErrorClass -> ErrorState
                _ -> panic $ "nextStateTable: no such class " <> show class_
            IdentifierState ->
              case class_ of
                AlphaClass -> IdentifierState
                NumericClass -> IdentifierState
                DotClass -> IdentifierDotState
                PrimeClass -> IdentifierState
                _ -> IdentifierDone
            IdentifierDotState ->
              case class_ of
                AlphaClass -> IdentifierState
                DotClass -> OperatorState
                MinusClass -> OperatorState
                OperatorClass -> OperatorState
                _ -> IdentifierDone
            NumberState ->
              case class_ of
                NumericClass -> NumberState
                _ -> NumberDone
            MinusState ->
              case class_ of
                NumericClass -> NumberState
                DotClass -> OperatorState
                PrimeClass -> ErrorState
                MinusClass -> SingleLineCommentState
                OperatorClass -> OperatorState
                _ -> OperatorDone
            LeftParenState ->
              LeftParenDone
            RightParenState ->
              LeftParenDone
            LeftBraceState ->
              case class_ of
                MinusClass -> MultiLineCommentState
                _ -> OperatorDone
            RightBraceState ->
              OperatorDone
            OperatorState ->
              case class_ of
                MinusClass -> OperatorState
                OperatorClass -> OperatorState
                _ -> OperatorDone
            SingleLineCommentState ->
              case class_ of
                NewlineClass -> InitialState
                EndOfFileClass -> EndOfFileDone
                _ -> SingleLineCommentState
            MultiLineCommentState ->
              case class_ of
                MinusClass -> MultiLineCommentMinusState
                EndOfFileClass -> ErrorDone
                _ -> MultiLineCommentState
            MultiLineCommentMinusState ->
              case class_ of
                RightBraceClass -> InitialState
                MinusClass -> MultiLineCommentMinusState
                EndOfFileClass -> ErrorDone
                _ -> MultiLineCommentState
            ErrorState ->
              case class_ of
                ErrorClass -> ErrorState
                PrimeClass -> ErrorState
                _ -> ErrorDone

            _ ->
              ErrorDone
      )
    off
  )
