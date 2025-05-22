module Main where

import LocalPrelude
import Data.Word
import Data.Int
import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Exception
import GHC.TypeLits

import Hedgehog ((===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty qualified as Tasty
import Test.Tasty.Hedgehog qualified as Tasty
import Text.Printf
import Text.Read

import Data.BitArray
import Data.Float hiding (Float, Double)
import Data.Float qualified as Soft
import Data.Bits

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable

main :: IO ()
main = Tasty.defaultMain $ Tasty.testGroup "Softfloat"
  [ Tasty.testProperty "noop" $ H.property $ return ()

  , Tasty.testGroup "Parsing"
    [ Tasty.testProperty "Unit tests" unitTest_floatParsing
    , Tasty.testProperty "Rountrip against native Float" prop_parsingRountripNativeFloat
    , Tasty.testProperty "Rountrip against native Double" prop_parsingRountripNativeDouble
    ]

  -- , Tasty.testProperty "parse/show matches native floats" prop_parseShowRoundtripNativeFloat
  , Tasty.testProperty "normalize mantissa" prop_normalizeMantissa

  -- rounding
  , Tasty.testProperty "bitlist rounding unit test" unitTest_bitlistRounding
  , Tasty.testProperty "no rounding" prop_shorterValuesNeedNoRounding
  ]

prop_parsingRountripNativeFloat :: H.Property
prop_parsingRountripNativeFloat = H.property $ do
  str <- H.forAll (randomDecimalString @Soft.Float)
  compareParsingAgainstNative @Float @Word32 @Soft.Float str

prop_parsingRountripNativeDouble :: H.Property
prop_parsingRountripNativeDouble = H.withTests 200 $ H.property $ do
  str <- H.forAll (randomDecimalString @Soft.Double)
  compareParsingAgainstNative @Double @Word64 @Soft.Double str

compareParsingAgainstNative
  :: forall native word softfloat b e m
  . ( Storable native, Read native, Show native            -- native type, e.g Float, Double
    , Storable word, FiniteBits word                       -- matching word, e.g Word32, Word64
    , FiniteBits softfloat, Read softfloat, Show softfloat, Bounded softfloat -- matching softfloat, e.g Finite 2 8 23
    , softfloat ~ Format b e m, KnownNat e
    ) => String -> H.PropertyT IO ()
compareParsingAgainstNative strFloat = do
  let native = readLabel "native" strFloat :: native
  w <- liftIO $ getStoredWord @native @word native
  let w' = readLabel "soft" strFloat :: softfloat
      isBoundMsg
        | w' == maxBound = " maxBound"
        | w' == minBound = " minBound"
        | otherwise = ""
      integerDigits = show . length . dropWhile (== '-') . takeWhile (/= '.')
      notes = unlines
        [ "strFloat " <> strFloat <> " (" <> integerDigits strFloat <> ")"
        , "native " <> showBits (intVal @e) w <> " " <> show native
        , "soft   " <> showBits (intVal @e) w' <> " " <> show w' <> " " <> isBoundMsg
        ]
  -- liftIO $ threadDelay 10000 >> putStrLn notes
  H.footnote notes
  bitListFinite w === bitListFinite w'
  where
    -- showBits :: Int -> Format b e m -> String
    showBits v x = unwords [show (head x'), show e, show m]
      where
        x' = bitListFinite x
        (e, m) = splitAt v (tail x')

hot :: IO ()
hot = main

getStoredWord :: forall from to . (Storable from, Storable to) => from -> IO to
getStoredWord f = do
  p :: Ptr from <- malloc @from
  poke p f
  peek (castPtr p)

-- * Parsing

-- | Test `normalizeMantissa`, a function used in float parsing, by
-- giving it an integer part bits and fraction part bits and testing
-- whether exponent is correct.
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

  let positiveExponent = toInteger (length (dropZeroes intBits)) - 1 === expDiff
      negativeExponent = negate (toInteger (length (takeWhile (== O) fracBits)) + 1) === expDiff

  if | _ : _ <- intBits                    -> do positiveExponent; result === intBits <> fracBits
     | _ : _ <- fracBits                   -> do negativeExponent; result === dropZeroes fracBits
     | []    <- intBits, []    <- fracBits -> do result === []; expDiff === 0

  where
    dropZeroes = dropWhile (== O)

unitTest_floatParsing :: H.Property
unitTest_floatParsing = unitTest $ do
  let read' str = readLabel "" str :: Binary16
  read' "0" === Format { sign = O, exponent = 0, mantissa = 0 } -- "0" parses as all zero field values for sign, exponent and mantissa
  read' "0" === 0b0                                             -- "0" parses as all zero bytes
  read' "0" === 0                                               -- same

  -- monomorphized `showDescribeFloat`
  let showDescribeFloat' :: Binary16 -> (String, String)
      showDescribeFloat' = showDescribeFloat

  showDescribeFloat' (readLabel "" "0") === ("0.0", "positive zero")
  showDescribeFloat' (readLabel "" "-0") === ("-0.0", "negative zero")
  showDescribeFloat' (Format O maxBound 0) === ("inf", "positive infinity")
  showDescribeFloat' (Format I maxBound 0) === ("-inf", "negative infinity")
  showDescribeFloat' (Format O maxBound 1) === ("snan", "positive signaling nan")
  showDescribeFloat' (Format I maxBound 1) === ("-snan", "negative signaling nan")
  showDescribeFloat' (Format O maxBound (1 + signalingBound @2 @10)) === ("nan", "positive nan")
  showDescribeFloat' (Format I maxBound (1 + signalingBound @2 @10)) === ("-nan", "negative nan")

  let f12 = read' "1.2"
  f12 === fromBits @Integer 0b0011110011001101
  show f12 === "1.2001953125"

  let f13 = read' "1.3"
  f13 === fromBits @Integer 0b0011110100110011
  show f13 === "1.2998046875"

  let f32 str = compareParsingAgainstNative @Float @Word32 @Binary32 str
  f32 "2.0"
  f32 "9223372036854775807.0"
  f32 "0.1"
  f32 "-9145438377800105983.0"
  f32 "340282356779733661637539395458142568448"

  -- Signaling NaNs' payload
  getPayload (Format O maxBound 123 :: Binary16) === Just (123 :: BitArray 9)
  getPayload (Format O maxBound 0b1001 :: Binary16) === Just (0b1001 :: BitArray 9)
  getPayload (Format O maxBound (1 + signalingBound @2 @10) :: Binary16) === Nothing

prop_parseShowRoundtripNativeFloat :: H.Property
prop_parseShowRoundtripNativeFloat = H.property $ do
  str <- H.forAll (randomDecimalString @Soft.Float)
  liftIO $ do
    threadDelay 5000
    putStrLn str
  show (readLabel "" str :: Binary32) === show (readLabel "" str :: Float)

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

-- * Helpers

runTest :: String -> H.Property -> IO ()
runTest msg test = Tasty.defaultMain $ Tasty.testGroup msg [ Tasty.testProperty msg test ]

bit_ :: H.MonadGen m => m Bit
bit_ = boolBit <$> Gen.bool

unitTest :: H.PropertyT IO () -> H.Property
unitTest test = H.withTests 1 $ H.property test

-- | Generate random decimal number as string, both negative and
-- positive and with or without the fraction part. E.g -9.2, 1, 8, 90842083.0
randomDecimalString
  :: forall t b e m m'
   . (t ~ Format b e m, KnownNat b, KnownNat e, KnownNat m, H.MonadGen m')
  => m' String
randomDecimalString = do
  addSign <- Gen.bool
  let minus x = '-' : show x
      plus x = show x
      sign :: Natural -> String
      sign x = (if addSign then "-" else "") <> show x

      maxNat = fromIntegral $ floatInt (maxBound :: t)
      minNat = fromIntegral $ abs $ floatInt (minBound :: t)

  int :: String <- Gen.choice
    [ fmap sign  $ Gen.integral $ Range.linear 0 maxNat -- big numbers
    , fmap sign  $ Gen.integral $ Range.linear 0 1000   -- small numbers
    , fmap sign  $ return (maxNat + 1000000000000000000000000000000000000000000) -- overflow
    , fmap plus  $ return maxNat -- max bound
    , fmap minus $ return minNat -- min bound
    , fmap sign  $ return 0
    , fmap sign  $ return 1
    ]

  addFraction <- Gen.bool
  if addFraction
    then do
      frac :: Word64 <- Gen.integral $ Range.linear minBound maxBound
      return $ int <> "." <> show frac
    else return int
