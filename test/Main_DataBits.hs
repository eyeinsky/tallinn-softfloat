module Main_DataBits where

import Prelude
import Data.Word
import Data.Bits

import Hedgehog ((===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty qualified as Tasty
import Test.Tasty.Hedgehog qualified as Tasty

import Data.Bit


tests =
  [ Tasty.testProperty "Basic unit tests" Main_DataBits.prop_roundEvenUnit
  , Tasty.testProperty "roundEven property test against arbitrary Word16" Main_DataBits.prop_roundEven
  ]

prop_roundEvenUnit :: H.Property
prop_roundEvenUnit = unitTest $ do
  round' 0b10000000 === -- down
         0b1000
  round' 0b11010000 === -- down
         0b1101
  round' 0b10001000 === -- tie, even => down/keep
         0b1000
  round' 0b10011000 === -- tie, odd => up/add
         0b1010
  round' 0b10001010 === -- up
         0b1001
  round' 0b11111100 === -- up, overflow
         0b10000
  where
    -- helper to round a word8 four places from right
    round' val = roundEven 4 val :: Word8

prop_roundEven :: H.Property
prop_roundEven = H.withTests 500 $ H.property $ do
  left' <- H.forAll Gen.enumBounded
  right' <- H.forAll Gen.enumBounded
  let
    left = fromIntegral @Word8 @Word16 left'
    right = fromIntegral @Word8 @Word16 right'

    w64 = shiftL left 8 .|. right
    res = roundEven 8 w64

  H.footnote $ unlines
    [ "left-right "  <> binaryLiteralChunked (repeat 8) left' <> " " <> binaryLiteralChunked (repeat 8) right'
    , "w64        "  <> binaryLiteralChunked (repeat 8) w64
    , "bit7       " <> binaryLiteralChunked (repeat 8) (bit 7 :: Word16)
    , "result     " <> binaryLiteralChunked (repeat 8) res
    ]

  let expected = case compare right (bit 7) of
        GT -> left + 1
        EQ -> if testBit left 0
          then left + 1
          else left
        LT -> left

  res === expected

-- * Helpers

unitTest :: H.PropertyT IO () -> H.Property
unitTest test = H.withTests 1 $ H.property test

bit_ :: H.MonadGen m => m Bit
bit_ = boolBit <$> Gen.bool

runTest :: H.Property -> IO ()
runTest test = Tasty.defaultMain $ Tasty.testGroup "runTest" [ Tasty.testProperty "runTest" test ]

runTests :: [Tasty.TestTree] -> IO ()
runTests tests = Tasty.defaultMain $ Tasty.testGroup "runTests" tests
