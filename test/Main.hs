{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import LocalPrelude
import Prelude qualified as Native (Float, Double)
import Data.Word
import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent
import GHC.TypeLits
import System.IO.Unsafe
import Foreign.Storable
import Text.Printf

import Hedgehog ((===))
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty qualified as Tasty
import Test.Tasty.Hedgehog qualified as Tasty

import Data.BitArray hiding (multiply)
import Data.Float hiding (Float, Double)
import Data.Float qualified as Soft
import Data.Bits

import Main_DataBits (bit_, unitTest, runTest, runTests)
import Main_DataBits qualified

-- import System.Random.SplitMix
-- import Test.QuickCheck.Random
-- mkSeed :: Word64 -> Word64 -> QCGen
-- mkSeed a b = QCGen $ seedSMGen a b


main :: IO ()
main = Tasty.defaultMain $ Tasty.testGroup "Softfloat"
  [ Tasty.testProperty "noop" $ H.property $ return ()

  , Tasty.testGroup "Data.Bits" Main_DataBits.tests

  , Tasty.testGroup "Parsing"
    [ Tasty.testProperty "Unit tests" unitTest_floatParsing
    , Tasty.testProperty "Rountrip against native Float" prop_parsingRountripNativeFloat
    , Tasty.testProperty "Rountrip against native Double" prop_parsingRountripNativeDouble
    , Tasty.testProperty "From binary" prop_parsingFromBinary
    ]

  , Tasty.testGroup "Operations"
    [ Tasty.testProperty "Multiplication" prop_multiply
    , Tasty.testProperty "Division" prop_division
    , Tasty.testProperty "Addition" prop_addition
    , Tasty.testProperty "Subtraction" prop_subtraction
    ]

  -- , Tasty.testProperty "parse/show matches native floats" prop_parseShowRoundtripNativeFloat
  , Tasty.testProperty "normalize mantissa" prop_normalizeMantissa

  -- rounding
  , Tasty.testProperty "bitlist rounding unit test" unitTest_bitlistRounding
  , Tasty.testProperty "no rounding" prop_shorterValuesNeedNoRounding
  ]

-- * Parsing

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
  w :: word <- liftIO $ viaStorable @native @word native
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
  let read' str = readLabel "" str :: Soft.Half
  read' "0" === Format { sign = O, exponent = 0, mantissa = 0 } -- "0" parses as all zero field values for sign, exponent and mantissa
  read' "0" === 0b0                                             -- "0" parses as all zero bytes
  read' "0" === 0                                               -- same

  -- monomorphized `showDescribeFloat`
  let showDescribeFloat' :: Soft.Half -> (String, String)
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
  f12 === fromBits_ @Integer 0b0011110011001101
  show f12 === "1.2001953125"

  let f13 = read' "1.3"
  f13 === fromBits_ @Integer 0b0011110100110011
  show f13 === "1.2998046875"

  let f32 str = compareParsingAgainstNative @Native.Float @Word32 @Soft.Float str
  f32 "2.0"
  f32 "9223372036854775807.0"
  f32 "0.1"
  f32 "-9145438377800105983.0"
  f32 "340282356779733661637539395458142568448"

  -- Signaling NaNs' payload
  snanPayload (Format O maxBound 123 :: Soft.Half) === Just (123 :: BitArray 9)
  snanPayload (Format O maxBound 0b1001 :: Soft.Half) === Just (0b1001 :: BitArray 9)
  snanPayload (Format O maxBound (1 + signalingBound @2 @10) :: Soft.Half) === Nothing

prop_parsingFromBinary :: H.Property
prop_parsingFromBinary = unitTest $ do
  let fromBits' :: Integer -> Soft.Format 2 3 4
      fromBits' = fromBits_

  show (nan @2 @3 @4) === "nan"
  show (snan @2 @3 @4 (0b101 :: BitArray 3)) === "snan"
  show (fromBits' 0b0_111_0000) === "inf"
  show (fromBits' 0b1_111_0000) === "-inf"
  show (fromBits' 0b0_111_1000) === "nan"
  show (fromBits' 0b0_111_0100) === "snan"
  snanPayload (fromBits' 0b0_111_0101) === Just 0b101

prop_parseShowRoundtripNativeFloat :: H.Property
prop_parseShowRoundtripNativeFloat = H.property $ do
  str <- H.forAll (randomDecimalString @Soft.Float)
  liftIO $ do
    threadDelay 5000
    putStrLn str
  show (readLabel "" str :: Soft.Float) === show (readLabel "" str :: Float)

-- * Operations

type Small = Format 2 3 3

delayed a = liftIO $ do
  threadDelay 1000
  a

hot :: IO ()
hot = do
  -- runTest unitTest_BitsInstance
  -- runTest unitTest_multiply
  -- H.recheckAt (H.Seed 16975537929181517343 15631089919146336913) "38:aC2bAiH20" prop_multiply
  -- H.recheckAt (H.Seed 5030941632379584368 14175235372969874745) "50:bA3fDcDc2IdC2" prop_multiply
  -- H.recheckAt (H.Seed 697175833316279477 8095718973563675341) "65:dAgCfDcE2c2" prop_multiply
  -- H.recheckAt (H.Seed 18221922921332819946 15611580718735075015) "68:bA6bC2a5Dc2DbA" prop_multiply -- sigMultOverflow
  H.recheckAt (H.Seed 10984703261618746247 10933244729112182337) "94:cAbCdA19" prop_multiply -- normal * subnormal = subnormal
  -- runTest prop_multiply

unitTest_addBias :: H.Property
unitTest_addBias = unitTest $ do
  return ()

unitTest_BitsInstance :: H.Property
unitTest_BitsInstance = unitTest $ do
  let
    test op a b = op (fromBits_ (a :: Natural) :: Small) === (fromBits_ (b :: Natural) :: Small)
  test (flip shiftR 1) 0b111000 0b11100
  test (flip shiftR 2) 0b111000  0b1110
  test (flip shiftR 3) 0b111000   0b111
  -- test (flip shiftR 4) 0b111000    0b11 -- TODO


desc :: String -> Format b e m -> String
desc label f = let
  (shown, described) = showDescribeFloat f
  bits = showFloatBits f
  in label <> "{" <> intercalate ", " [shown, bits, described] <> "}"

makeNote :: Format b e m -> Format b e m -> Format b e m -> Format b e m -> [String] -> String
makeNote a b expected result debug =
  unlines $
    [ unwords [ "operation:", desc "a" a, "*", desc "b" b, "=", desc "expected" expected ]
    , "expected " <> showFloatBits expected
    , "result   " <> showFloatBits result
    ] <> debug

unitTest_multiply :: H.Property
unitTest_multiply = unitTest $ do
  let
    small b = fromBits_ (b :: Natural) :: Small

    test :: Natural -> Natural -> Small -> H.PropertyT IO ()
    test a' b' expected = do
      let a = fromBits_ a' :: Small
          b = fromBits_ b' :: Small
          (debug, result) = multiply a b
          note = makeNote a b expected result debug
      H.footnote note
      -- delayed $ putStrLn note
      result === expected

    test_ :: Small -> Natural -> Small -> Natural -> Small -> Natural -> H.PropertyT IO ()
    test_ a aNat b bNat expected expectedNat = do
      let a' = fromBits_ aNat
          b' = fromBits_ bNat
          expected' = fromBits_ expectedNat
          (debug, result) = multiply a b
          note = makeNote a b expected result debug
      H.footnote note
      -- delayed $ putStrLn note
      a === a'
      b === b'
      expected === expected'
      result === expected

  let f_9 = 0b0110001
      f_0'0625 = small 0b0_000_010

  test 0b0001111 0b0001111 f_0'0625 -- exponents underflow, rounding overflows

  -- actual calcualtion tests:
  test_ 0.5 0b0_010_000 0.5 0b0_010_000 0.25 0b0_001_000 -- 0.5 * 0.5 = 0.25
  test 0b0001000 0b0001000 f_0'0625 -- two normal floats amount to a subnormal 0.25 * 0.25 = 0.0625
  test 0b0011000 0b0011000 1 -- 1 * 1 = 1
  test 0b0110000 0b0110000 inf -- exponent overflow is infinity: exponent is already maxed out at 3 (0b110)

  -- special case tests:
  test 0b0111100 f_9      nan -- nan * _
  test f_9       0b0111001 nan -- _ * nan
  test 0b0111000 0         nan -- _ * nan
  test 0b0111000 0b1111000 (negate inf) -- inf * -inf = -inf
  test 0b0111000 f_9      inf
  test f_9      0b1111000 (negate inf)


prop_multiply :: H.Property
-- prop_multiply = H.property $ do
prop_multiply = H.withTests 10000 $ H.property $ do
-- prop_multiplication = unitTest $ do
  (sf1, nf1) <- H.forAll softNativePair
  (sf2, nf2) <- H.forAll softNativePair
  -- let sf = sf1 * sf2
  let (debug, sf) = multiply sf1 sf2
  let nf = nf1 * nf2
  nfw <- liftIO $ viaStorable @Float @Word32 nf

  let notes = unlines $ debug <>
        [ "native: " <> show nf <> " = " <> show nf1 <> " * " <> show nf2
        , l "binaryNatural soft   bits" $ BitArray @32 (binaryNatural sf)
        , l "binaryNatural native bits" $ BitArray @32 (binaryNatural nfw)
        ]
      note = makeNote sf1 sf2 (fromBits_ nfw) sf debug
  -- liftIO $ threadDelay 10000 >> putStrLn notes

  H.footnote note

  binaryNatural sf === binaryNatural nfw

bl a = binaryLiteralChunked [1, 8, 23] a

prop_addition :: H.Property
prop_addition = H.property $ do
  return ()

prop_subtraction :: H.Property
prop_subtraction = H.property $ do
  return ()

prop_division :: H.Property
prop_division = H.property $ do
  return ()

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
      (rounded, extraDigit) = roundBits roundToLength value

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
          O : _rest -> True
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

anyFloat :: forall m . H.MonadGen m => m Soft.Float
anyFloat = do
  str <- randomDecimalString @Soft.Float
  return (readLabel "anyFloat" str)

anyFloat2
  :: forall f w (b :: Natural) (e :: Natural) (m :: Natural) m'
   . ( KnownNat b, KnownNat e, KnownNat m
     , Soft.MatchingWord f ~ w, f ~ Format b e m
     , H.MonadGen m'
     , Enum w, Bounded w, Bits w)
  => m' f
anyFloat2 = do
  fromBits_ <$> (Gen.enumBounded @m' @w)

-- yyy

softNativePair :: (H.MonadGen m') => m' (Soft.Float, Float)
softNativePair = do
  soft <- normalSoftfloat
  let native = unsafePerformIO $ viaStorable (toBits soft)
  return (soft, native)

softToNative :: Soft.Float -> Native.Float
softToNative soft = unsafePerformIO $ viaStorable (toBits soft)

-- | Generate a regular finite float, i., not a special value (nan, inf) nor a subnormal finite float.
normalSoftfloat :: forall m' b e m . (H.MonadGen m', KnownNat b, KnownNat e, KnownNat m) => m' (Format b e m)
normalSoftfloat =
  Format
    <$> bit_
    <*> Gen.integral (Range.linear 0 maxBound)
    <*> Gen.integral (Range.linear 0 maxBound)

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
    , fmap minus $ return (minNat :: Integer) -- min bound
    , fmap sign  $ return 0
    , fmap sign  $ return 1
    ]

  addFraction <- Gen.bool
  if addFraction
    then do
      frac :: Word64 <- Gen.integral $ Range.linear minBound maxBound
      return $ int <> "." <> show frac
    else return int
