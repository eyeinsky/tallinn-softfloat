module Main where

import LocalPrelude
import Data.Word
import Control.Monad
import Control.Monad.IO.Class

import Hedgehog ((===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty qualified as Tasty
import Test.Tasty.Hedgehog qualified as Tasty

import Data.BitArray
import Data.Float


main :: IO ()
main = Tasty.defaultMain $ Tasty.testGroup "shoftfloat"
  [ Tasty.testProperty "noop" $ H.property $ return ()
  -- rounding
  , Tasty.testProperty "bitlist rounding unit test" unitTest_bitlistRounding
  , Tasty.testProperty "no rounding" prop_shorterValuesNeedNoRounding
  -- parsing, rendering
  , Tasty.testProperty "unit test: float parsing" unitTest_floatParsing
  , Tasty.testProperty "parse/show matches native floats" prop_parseShowRoundtripNativeFloat
  ]

unitTest_floatParsing :: H.Property
unitTest_floatParsing = unitTest $ do
  let read' str = read str :: Binary16
  read' "0" === zero
  read' "0" === 0
  describe' (read "0") === ("0", "positive zero")
  describe' (read "-0") === ("-0", "negative zero")
  describe' (Finite O maxBound 0) === ("inf", "positive infinity")
  describe' (Finite I maxBound 0) === ("-inf", "negative infinity")
  describe' (Finite O maxBound 1) === ("snan", "positive signaling nan")
  describe' (Finite I maxBound 1) === ("-snan", "negative signaling nan")
  describe' (Finite O maxBound (1 + signalingBound @2 @10)) === ("nan", "positive nan")
  describe' (Finite I maxBound (1 + signalingBound @2 @10)) === ("-nan", "negative nan")

  let f12 = read' "1.2"
  f12 === fromBits @Integer 0b0011110011001101
  show f12 === "1.2001953125"

  let f13 = read' "1.3"
  f13 === fromBits @Integer 0b0011110100110011
  show f13 === "1.2998046875"

  -- Signaling NaNs' payload
  getPayload (Finite O maxBound 123 :: Binary16) === Just (123 :: BitArray 9)
  getPayload (Finite O maxBound 0b1001 :: Binary16) === Just (0b1001 :: BitArray 9)
  getPayload (Finite O maxBound (1 + signalingBound @2 @10) :: Binary16) === Nothing

  where
    describe' :: Binary16 -> (String, String)
    describe' = showDescribeFloat

unitTest_bitlistRounding :: H.Property
unitTest_bitlistRounding = unitTest $ do
  -- Implement cases from here: https://stackoverflow.com/a/75102483/4126514
  let test bits = let
        (a, b) = span (== O) $ reverse bits -- remove trailing zeroes
        (bits', overflow) = roundBits 4 $ reverse b -- round to 4 digits
        bits'' = bits' <> replicate (length a) O -- re-add trailing zeroes
        bits''' = take (if overflow then 5 else 4) bits''
        in (bits''', overflow)
  test [I, O,O,O, O,O,O,O] ===   ([I, O,O,O], False) -- down
  test [I, I,O,I, O,O,O,O] ===   ([I, I,O,I], False) -- down
  test [I, O,O,O, I,O,O,O] ===   ([I, O,O,O], False) -- tie
  test [I, O,O,I, I,O,O,O] ===   ([I, O,I,O], False) -- tie
  test [I, O,O,O, I,O,I,O] ===   ([I, O,O,I], False) -- up
  test [I, I,I,I, I,I,O,O] === ([I,O, O,O,O], True)  -- up, overflow

-- | Round a list of bits.
prop_shorterValuesNeedNoRounding :: H.Property
prop_shorterValuesNeedNoRounding = H.property $ do
  more <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  less <- H.forAll $ Gen.integral $ Range.linear @Int 0 more
  bits <- H.forAll $ replicateM less bit_
  roundBits more bits === (bits, False) -- False = no overflow

prop_parseShowRoundtripNativeFloat :: H.Property
prop_parseShowRoundtripNativeFloat = H.property $ do
  int :: Word32 <- H.forAll $ Gen.enumBounded
  frac :: Word32 <- H.forAll $ Gen.enumBounded
  let str = show int <> "." <> show frac
  liftIO $ putStrLn str
  show (read str :: Binary32) === show (read str :: Float)

-- * Helpers

bit_ :: H.MonadGen m => m Bit
bit_ = boolBit <$> Gen.bool

unitTest :: H.PropertyT IO () -> H.Property
unitTest test = H.withTests 1 $ H.property test

spaces :: Int -> String
spaces n = replicate n ' '
