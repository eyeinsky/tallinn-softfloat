module Main where

import LocalPrelude
import Data.Word
import Data.Int
import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent

import Hedgehog ((===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty qualified as Tasty
import Test.Tasty.Hedgehog qualified as Tasty

import Data.BitArray
import Data.Float hiding (Float, Double)
import Data.Float qualified as Soft
import Data.Bits

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable

main :: IO ()
main = Tasty.defaultMain $ Tasty.testGroup "shoftfloat"
  [ Tasty.testProperty "noop" $ H.property $ return ()

  -- parsing, rendering
  , Tasty.testProperty "unit test: float parsing" unitTest_floatParsing
  -- , Tasty.testProperty "parse/show matches native floats" prop_parseShowRoundtripNativeFloat
  , Tasty.testProperty "normalize mantissa" prop_normalizeMantissa

  -- parsing
  , Tasty.testProperty
    "Parsing floats from string results in same binary representation as native"
    prop_parsingEquvalentToNative

  -- rounding
  , Tasty.testProperty "bitlist rounding unit test" unitTest_bitlistRounding
  , Tasty.testProperty "no rounding" prop_shorterValuesNeedNoRounding
  ]

-- runTest :: H.Property -> IO ()
runTest msg test = Tasty.defaultMain $ Tasty.testGroup msg [ Tasty.testProperty "test" test ]

prop_parsingEquvalentToNative :: H.Property
prop_parsingEquvalentToNative = H.property $ do
  str <- H.forAll randomDecimalString
  compareParsingAgainstNative @Float @Word32 @Binary32 str
  compareParsingAgainstNative @Double @Word64 @Binary64 str


compareParsingAgainstNative
  :: forall native word softfloat
  . ( Storable native, Read native         -- native type, e.g Float, Double
    , Storable word, FiniteBits word       -- matching word, e.g Word32, Word64
    , FiniteBits softfloat, Read softfloat -- matching softfloat, e.g Finite 2 8 23
    ) => String -> H.PropertyT IO ()
compareParsingAgainstNative strFloat = do
  w <- liftIO $ getStoredWord @native @word $ read strFloat
  let w' = read strFloat :: softfloat
      notes = unlines
        [ "strFloat " <> strFloat
        , "native " <> showBits w
        , "soft   " <> showBits w'
        ]
  liftIO $ threadDelay 10000 >> putStrLn notes
  H.footnote notes
  bitListFinite w === bitListFinite w'

showBits x = unwords [show (head x'), show e, show m]
  where
    x' = bitListFinite x
    (e, m) = splitAt 8 (tail x')

hot = do
  -- main
  -- threadDelay 1000000000
  runTest "" $ H.property $
    compareParsingAgainstNative @Float @Word32 @Binary32 "9223372036854775807.0"

--  let (debug, (f :: Soft.Float, leftover)) = parseFloat "2.0"
  -- putStrLn $ unlines debug
  -- putStrLn $ showBits f
  -- print ()

{-
strFloat  9223372036854775807.0
native O [I,O,O,O,O,I,I,I] [I,I,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O]
soft   O [I,O,O,O,O,I,I,I] [I,O,I,I,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O]
strFloat -9223372036854775808.0
native I [I,O,I,I,I,I,I,O] [O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O]
soft   I [I,O,I,I,I,I,I,O] [O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,O,This]
-}

getStoredWord :: forall from to . (Storable from, Storable to) => from -> IO to
getStoredWord f = do
  p :: Ptr from <- malloc @from
  poke p f
  peek (castPtr p)

-- * Parsing

-- | Test `normalizeMantissa`, a function used in float parsing, by
-- giving it an integer part bits and fraction part bits and testing
-- whether exponent is correct and if initial implicit bit is dropped.
prop_normalizeMantissa :: H.Property
prop_normalizeMantissa = H.property $ do
  intPartLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  fracPartLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  intBits' <- H.forAll $ replicateM intPartLength bit_
  fracBits' <- H.forAll $ replicateM fracPartLength bit_

  let intBits = dropWhile (== O) intBits'
      fracBits = reverse $ dropWhile (== O) $ reverse fracBits'
      (result, expDiff) = normalizeMantissa intBits fracBits

  H.footnote $ unlines
    [ "intBits " <> show intBits
    , "fracBits " <> show fracBits
    , "expDiff " <> show expDiff
    , "result " <> show result
    ]

  let positiveExponent = length (dropZeroes intBits) - 1 === expDiff
      negativeExponent = negate (length (takeWhile (== O) fracBits) + 1) === expDiff

  if | _ : _ <- intBits                    -> do positiveExponent; result === drop 1 (intBits <> fracBits)
     | _ : _ <- fracBits                   -> do negativeExponent; result === drop 1 (dropZeroes fracBits)
     | []    <- intBits, []    <- fracBits -> do result === []; expDiff === 0

  where
    dropZeroes = dropWhile (== O)

unitTest_floatParsing :: H.Property
unitTest_floatParsing = unitTest $ do
  let read' str = read str :: Binary16
  read' "0" === Finite { sign = O, exponent = 0, mantissa = 0 } -- "0" parses as all zero field values for sign, exponent and mantissa
  read' "0" === 0b0                                             -- "0" parses as all zero bytes
  read' "0" === 0                                               -- same

  -- monomorphized `showDescribeFloat`
  let showDescribeFloat' :: Binary16 -> (String, String)
      showDescribeFloat' = showDescribeFloat

  showDescribeFloat' (read "0") === ("0.0", "positive zero")
  showDescribeFloat' (read "-0") === ("-0.0", "negative zero")
  showDescribeFloat' (Finite O maxBound 0) === ("inf", "positive infinity")
  showDescribeFloat' (Finite I maxBound 0) === ("-inf", "negative infinity")
  showDescribeFloat' (Finite O maxBound 1) === ("snan", "positive signaling nan")
  showDescribeFloat' (Finite I maxBound 1) === ("-snan", "negative signaling nan")
  showDescribeFloat' (Finite O maxBound (1 + signalingBound @2 @10)) === ("nan", "positive nan")
  showDescribeFloat' (Finite I maxBound (1 + signalingBound @2 @10)) === ("-nan", "negative nan")

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

prop_parseShowRoundtripNativeFloat :: H.Property
prop_parseShowRoundtripNativeFloat = H.property $ do
  str <- H.forAll randomDecimalString
  liftIO $ do
    threadDelay 5000
    putStrLn str
  show (read str :: Binary32) === show (read str :: Float)

-- * Rounding

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

-- | Test `roundBits`: round the bitlist `bits` generated to be to `more`
prop_shorterValuesNeedNoRounding :: H.Property
prop_shorterValuesNeedNoRounding = H.property $ do
  bitsLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  bits <- H.forAll $ replicateM bitsLength bit_
  moreThanBitsLength <- H.forAll $ Gen.integral $ Range.linear @Int bitsLength (bitsLength + 10)
  roundBits moreThanBitsLength bits === (bits, False)

-- | Comprehensive test for `roundBits`.
prop_longerValuesRoundCorrectly :: H.Property
prop_longerValuesRoundCorrectly = H.property $ do
  roundToLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  bits <- H.forAll $ replicateM roundToLength bit_
  overflowLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  overflow <- H.forAll $ replicateM overflowLength bit_
  let value = bits <> overflow
      res@(rounded, extraDigit) = roundBits roundToLength value

  H.footnote $ "extraDigit " <> show extraDigit
  H.footnote $ "rounded value " <> show rounded
  H.footnote $ "constructed value " <> show value <> " " <> show (bits, overflow) <> ", rounded to " <> show roundToLength

  let overflowIsTie = case overflow of
        I : rest -> all (O ==) rest
        _ -> False
      overflowIsMoreThanHalf = case overflow of
        I : rest -> any (I ==) rest
        _ -> False
      remainderIsEven = case bits of
        [] -> True
        _ -> case reverse bits of
          O : rest -> True
          _ -> False
      mustRoundUp = overflowIsMoreThanHalf || overflowIsTie && not remainderIsEven

  if
    | mustRoundUp -> do
        bits H./== value
        reverse (fst (add1 (reverse bits))) === rounded
        when extraDigit $ H.assert $ all (== I) bits
    | not mustRoundUp -> do
        bits === rounded
        extraDigit === False
    | otherwise -> H.footnote "This never happens." >> H.failure

-- * Values

-- | Half, parsed from 0.1 by float.exposed
fe_0p1 = fromIntegerBits 0b0_01011_1001100110 :: Half


-- * Helpers

bit_ :: H.MonadGen m => m Bit
bit_ = boolBit <$> Gen.bool

unitTest :: H.PropertyT IO () -> H.Property
unitTest test = H.withTests 1 $ H.property test

spaces :: Int -> String
spaces n = replicate n ' '

randomDecimalString :: H.MonadGen m => m String
randomDecimalString = do
  int :: Int64 <- Gen.choice
    [ Gen.integral $ Range.linear minBound maxBound
    , return 0
    ]
  frac :: Word64 <- Gen.integral $ Range.linear minBound maxBound
  return $ show int <> "." <> show frac
  -- -- return $ show int <> "." <> show frac
  -- return "0.1"

-- generate integral value between bounds
-- minMaxRange = Gen.choice
--   [ Gen.integral $ Range.linear minBound maxBound
--   , return minBound
--   , return maxBound
--   ]
