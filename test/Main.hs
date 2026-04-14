{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash #-}
module Main where

import LocalPrelude
import Prelude qualified as Native
import Data.Word
import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent
import GHC.TypeLits
import Foreign.Storable
import Foreign.Marshal
import GHC.Exts (double2Float#, Double(D#), Float(F#))
import System.IO.Unsafe

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

import Main_DataBits (bit_, unitTest, runTest)
import Main_DataBits qualified

-- import System.Random.SplitMix
-- import Test.QuickCheck.Random
-- mkSeed :: Word64 -> Word64 -> QCGen
-- mkSeed a b = QCGen $ seedSMGen a b


main :: IO ()
main = Tasty.defaultMain $ Tasty.testGroup "Softfloat"
  [ Tasty.testProperty "noop" $ H.property $ return ()

  , Tasty.testGroup "Data.Bits" Main_DataBits.tests

  , Tasty.testGroup "Printer/parser"
    [ Tasty.testProperty "Unit tests" unitTest_floatParsing
    , Tasty.testProperty "Rountrip against native Float" prop_parsingRountripNativeFloat
    , Tasty.testProperty "Rountrip against native Double" prop_parsingRountripNativeDouble
    , Tasty.testProperty "From binary" prop_parsingFromBinary
    ]

  , Tasty.testGroup "Misc"
    [ Tasty.testProperty "Storable peek/poke roundtrip" prop_storablePeekPokeRoundtrip
    ]

  , Tasty.testGroup "Generators & misc"
    [ Tasty.testProperty "subnormals" prop_generateSubnormals
    , Tasty.testProperty "quiet NaNs" prop_qnans
    , Tasty.testProperty "signalling NaNs" prop_snans
    ]

  , Tasty.testGroup "Arithmetic"
    [ Tasty.testProperty "Multiplication" $ disable prop_multiply
    , Tasty.testProperty "Division" prop_division
    , Tasty.testProperty "Addition" prop_addition
    , Tasty.testProperty "Subtraction" prop_subtraction
    , Tasty.testProperty "Truncation" prop_truncation
    ]

  -- , Tasty.testProperty "parse/show matches native floats" prop_parseShowRoundtripNativeFloat
  , Tasty.testProperty "normalize mantissa" prop_normalizeMantissa

  -- rounding
  , Tasty.testGroup "Rounding"
    -- bitlist
    [ Tasty.testProperty "bitlist rounding unit test" unitTest_bitlistRounding
    , Tasty.testProperty "no rounding" prop_shorterValuesNeedNoRounding
    -- binary
    , Tasty.testProperty "Binary rounding" unitTest_roundBinary
    -- soft vs native
    , Tasty.testProperty "soft vs native" prop_identicalSoftAndNativeRounding
    ]
  ]

-- * Misc

prop_generateSubnormals :: H.Property
prop_generateSubnormals = H.property $ do
  H.forAll (anyNativeWidth genSubnormal) >>= withAnyWidth (H.assert . isSubnormal)
  H.forAll (genSubnormal @Soft.Binary128) >>= H.assert . isSubnormal
  H.forAll (genSubnormal @Soft.Binary256) >>= H.assert . isSubnormal

prop_qnans :: H.Property
prop_qnans = H.property $ do
  H.forAll (anyNativeWidth genQNan) >>= withAnyWidth (H.assert . isQNan)

prop_snans :: H.Property
prop_snans = H.property $ do
  H.forAll (anyNativeWidth genSNan) >>= withAnyWidth (H.assert . isJust . snanPayload)

prop_storablePeekPokeRoundtrip :: H.Property
prop_storablePeekPokeRoundtrip = H.property $ do
  H.forAll (anyNativeWidth genFloat) >>= \case
    F16 f -> go f
    F32 f -> go f
    F64 f -> go f
  where
    go :: forall b e m .
      ( KnownNats b e m
      , KnownNat (Width (Format b e m))
      , Storable (ToWord (Width (Format b e m)))
      , Bits (ToWord (Width (Format b e m)))
      , HasPrecisionLabel (Format b e m)
      ) => Format b e m -> H.PropertyT IO ()
    go f = do
      f' <- liftIO $ do
        ptr <- malloc
        poke ptr f
        peek ptr
      f === f'

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
    , softfloat ~ Format b e m, KnownNat e, Integral word, KnownNats b e m, HasPrecisionLabel (Format b e m)
    ) => String -> H.PropertyT IO ()
compareParsingAgainstNative strFloat = do
  let native = readLabel "native" strFloat :: native
      w :: word = viaStorable @native @word native
  let w' = readLabel "soft" strFloat :: softfloat
      isBoundMsg
        | w' == maxBound = " maxBound"
        | w' == minBound = " minBound"
        | otherwise = ""
      integerDigits = show . length . dropWhile (== '-') . takeWhile (/= '.')
      notes = unlines
        [ "strFloat " <> strFloat <> " (" <> integerDigits strFloat <> ")"
        , "native " <> binaryLiteralChunked [1, intVal @e] w <> " " <> show native
        , "soft   " <> showFloatBits w' <> " " <> show w' <> " " <> isBoundMsg
        ]
  -- liftIO $ threadDelay 10000 >> putStrLn notes
  H.footnote notes
  bitListFinite w === bitListFinite w'

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
  showDescribeFloat' (Format O maxBound (1 + signalingBound @2 @10)) === ("nan", "positive quiet nan")
  showDescribeFloat' (Format I maxBound (1 + signalingBound @2 @10)) === ("-nan", "negative quiet nan")

  let f12 = read' "1.2"
  f12 === fromBits @Integer 0b0011110011001101
  show f12 === "1.2001953125"

  let f13 = read' "1.3"
  f13 === fromBits @Integer 0b0011110100110011
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
      fromBits' = fromBits

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

delayed :: MonadIO m => IO a -> m a
delayed a = liftIO $ do
  threadDelay 1000
  a

hot :: IO ()
hot = do
  -- unsafePerformIO $
  -- putStrLn $ showFloatBits_ (roundFloat (fromBits @Natural 0b_010_000 :: Format 2 3 3) :: Format 2 2 2)
  return ()
  runTest "unitTest_roundFloat" unitTest_roundFloat
  -- let b (n :: Natural) = fromBits n :: Format 2 3 3

  --     round :: Format 2 3 3 -> (Format 2 3 3, Format 2 2 2)
  --     round f = (f, unsafePerformIO $ roundFloat f)

  --     showFloatBits' f = showFloatBits f <> ", " <> describeFloat f

  --     test :: Format 2 3 3 -> IO ()
  --     test f = do
  --       let (a, b) = round f
  --       putStrLn $ "\n\n" <> unlines [showFloatBits' a, showFloatBits' b]

  -- liftIO $ test $ b 0b_0_011_000

-- unitTest_addBias :: H.Property
-- unitTest_addBias = unitTest $ do
--   (sd, nd) <- H.forAll (softNativePair @Soft.Double)
--   return ()

unitTest_BitsInstance :: H.Property
unitTest_BitsInstance = unitTest $ do
  let
    test op a b = op (fromBits (a :: Natural) :: Small) === (fromBits (b :: Natural) :: Small)
  test (flip shiftR 1) 0b111000 0b11100
  test (flip shiftR 2) 0b111000  0b1110
  test (flip shiftR 3) 0b111000   0b111
  -- test (flip shiftR 4) 0b111000    0b11 -- TODO


desc :: HasPrecisionLabel (Format b e m) => String -> Format b e m -> String
desc label f@Format{} = let
  (shown, described) = showDescribeFloat f
  bits = showFloatBits f
  in label <> "{" <> intercalate ", " [shown, bits, described] <> "}"

makeNote :: HasPrecisionLabel (Format b e m) => Format b e m -> Format b e m -> Format b e m -> Format b e m -> [String] -> String
makeNote a b expected@Format{} result debug =
  unlines $
    [ unwords [ "operation:", desc "a" a, "*", desc "b" b, "=", desc "expected" expected ]
    , "expected " <> showFloatBits expected
    , "result   " <> showFloatBits result
    ] <> debug

unitTest_multiply :: H.Property
unitTest_multiply = unitTest $ do
  let
    small b = fromBits (b :: Natural) :: Small

    test :: Natural -> Natural -> Small -> H.PropertyT IO ()
    test a' b' expected = do
      let a = fromBits a' :: Small
          b = fromBits b' :: Small
          (debug, result) = multiply a b
          note = makeNote a b expected result debug
      H.footnote note
      -- delayed $ putStrLn note
      result === expected

    test_ :: Small -> Natural -> Small -> Natural -> Small -> Natural -> H.PropertyT IO ()
    test_ a aNat b bNat expected expectedNat = do
      let a' = fromBits aNat
          b' = fromBits bNat
          expected' = fromBits expectedNat
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
  (sf1, nf1) <- H.forAll (softNativePair @Soft.Float)
  (sf2, nf2) <- H.forAll softNativePair
  -- let sf = sf1 * sf2
  let (debug, sf) = multiply sf1 sf2
  let nf = nf1 * nf2
      nfw = viaStorable @Float @Word32 nf

  let
      -- notes = unlines $ debug <>
      --   [ "native: " <> show nf <> " = " <> show nf1 <> " * " <> show nf2
      --   , l "binaryNatural soft   bits" $ BitArray @32 (binaryNatural sf)
      --   , l "binaryNatural native bits" $ BitArray @32 (binaryNatural nfw)
      --   ]
      note = makeNote sf1 sf2 (fromBits nfw) sf debug
  -- liftIO $ threadDelay 10000 >> putStrLn notes

  H.footnote note

  binaryNatural sf === binaryNatural nfw

prop_addition :: H.Property
prop_addition = H.property $ do
  return ()

prop_subtraction :: H.Property
prop_subtraction = H.property $ do
  return ()

prop_division :: H.Property
prop_division = H.property $ do
  return ()

prop_truncation :: H.Property
prop_truncation = H.property $ do
  (sf, nf) <- H.forAll $ softNativePair @Soft.Float
  H.footnote $ unlines
    [ show (sf, nf)
    , "sf: " ++ showFloatBits sf
    , "nf: " ++ showFloatBits nf
    ]
  truncate @_ @Integer sf === truncate nf

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
  test [I, O,O,O, O,O,O,O] === ([  I, O,O,O], False) -- down
  test [I, I,O,I, O,O,O,O] === ([  I, I,O,I], False) -- down
  test [I, O,O,O, I,O,O,O] === ([  I, O,O,O], False) -- tie
  test [I, O,O,I, I,O,O,O] === ([  I, O,I,O], False) -- tie
  test [I, O,O,O, I,O,I,O] === ([  I, O,O,I], False) -- up
  test [I, I,I,I, I,I,O,O] === ([I,O, O,O,O], True ) -- up, overflow

-- | Test `roundBits`: round the bitlist `bits` generated to be to `more`
prop_shorterValuesNeedNoRounding :: H.Property
prop_shorterValuesNeedNoRounding = H.property $ do
  bitsLength <- H.forAll $ Gen.integral $ Range.linear @Int 0 10
  bits <- H.forAll $ replicateM bitsLength bit_
  moreThanBitsLength <- H.forAll $ Gen.integral $ Range.linear @Int bitsLength (bitsLength + 10)
  roundBits moreThanBitsLength bits === (bits, False)

-- | Same test cases as for unitTest_bitlistRounding, but for any Bits instance.
unitTest_roundBinary :: H.Property
unitTest_roundBinary = unitTest $ do
  let test :: BitArray 8 -> (BitArray 8, Bool)
      test bits = roundEvenOverflow 4 bits
  test 0b_1000_0000 === ( 0b_1000, False) -- down
  test 0b_1101_0000 === ( 0b_1101, False) -- down
  test 0b_1000_1000 === ( 0b_1000, False) -- tie
  test 0b_1001_1000 === ( 0b_1010, False) -- tie
  test 0b_1000_1010 === ( 0b_1001, False) -- up
  test 0b_1111_1100 === (0b_10000, True ) -- up, overflow

type Tiny = Format 2 3 3

unitTest_roundFloat :: H.Property
unitTest_roundFloat = unitTest $ do
  let b (n :: Natural) = fromBits n :: Format 2 3 3
      test :: Word8 -> Natural -> H.PropertyT IO ()
      test input_ expected_ = let
        input = fromBits input_ :: Format 2 3 3
        rounded = roundFloat input :: Format 2 2 2
        expected = fromBits expected_ :: Format 2 2 2
        in do
        H.footnote $ unlines
          [ "input:    " <> showFloatBits_ input
          , "rounded:  " <> showFloatBits_ rounded
          , "expected: " <> showFloatBits_ expected
          ]
        toBitArray @5 rounded === toBitArray expected

  test 0b_0_011_000 -- normal -> normal
       0b_0__01_00

  test 0b_0_010_000 -- normal -> subnormal, 0.5 -> 0.5
       0b_0__00_10

  test 0b_0_000_100 -- subnormal -> subnormal
       0b_0__00_10

  return ()

showFloatBits_ f = intercalate ", " [showFloatBits f, describeFloat f, show f]

bf :: forall float b e m . (float ~ Format b e m, KnownNats b e m) => Natural -> float
bf (n :: Natural) = fromBits n -- :: Format 2 3 3

floatInfo :: forall float b e m . (float ~ Format b e m, KnownNats b e m) => IO ()
floatInfo = do
  putStrLn $ "min/max exponent " <> show (minExponent @e, maxExponent @e)
  putStrLn $ "bias " <> let bias'@(BitArray n) = bias @e in show (bias', n)
  putStrLn $ "min/max float " <> show (minBound @float, maxBound @float)
  putStrLn $ "around zero " <> show (setBit zeroBits 0 :: float)

uinitTest_identicalSoftAndNativeRounding :: H.Property
uinitTest_identicalSoftAndNativeRounding = unitTest $ do
  testDoubleFloatRounding (Format O maxBound (setMSB 0 + 12345678919) :: Soft.Double)

testDoubleFloatRounding sd = do
  () === ()
  -- let
  --     nd = toNative sd
  --     nf = double2Float nd
  --     sf = undefined -- roundFloat sd :: Soft.Float

  -- H.footnote $ unlines
  --   [ "sd " <> showFloatBits sd <> " " <> showCat sd
  --   , "nd " <> showFloatBits nd <> " " <> show nd
  --   , "nf " <> showFloatBits nf <> " " <> show nf
  --   , "sf " <> showFloatBits sf <> " " <> showCat sf
  --   ]

  -- undefined -- todo
--  toWord nf === toWord sf -- !!! Need to compare the underlying binary form as identical IEEE-754 NaNs don't compare equal to each other.

showCat :: Format b e m -> String
showCat f = show f <> ", " <> snd (showDescribeFloat f)

prop_identicalSoftAndNativeRounding :: H.Property
prop_identicalSoftAndNativeRounding = H.property $ do
  sd :: Soft.Double <- H.forAll genFloat
  testDoubleFloatRounding sd

double2Float :: Double -> Float
double2Float (D# d) = F# (double2Float# d)

-- | Comprehensive test for `roundBits`. TODO: why not listed in the tests?
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

-- * Generators

-- ** Basic

genFloat :: forall b e m m' . (KnownNats b e m, H.MonadGen m') => m' (Format b e m)
genFloat = Gen.choice $ genNormal : genSubnormal : map pure [zero, negate zero, inf, negate inf, nan]

-- | Generate a normal finite float. I.e, neither a special value (nan, inf) nor a subnormal.
genNormal :: forall m' b e m . (H.MonadGen m', KnownNats b e m) => m' (Format b e m)
genNormal =
  Format
    <$> bit_
    <*> Gen.integral (Range.linear 0 maxBound)
    <*> Gen.integral (Range.linear 0 maxBound)

genSubnormal :: forall f m' b e m . (f ~ Format b e m, H.MonadGen m', KnownNats b e m) => m' (Format b e m)
genSubnormal = formatEMS 0 <$> Gen.integral (Range.linear 1 maxBound) <*> bit_

formatEMS :: (KnownNats b e m) => BitArray e -> BitArray m -> Bit -> Format b e m
formatEMS e m s = Format s e m

-- TODO: add tests
genInf, genNan, genQNan :: forall m' b e m . (H.MonadGen m', KnownNats b e m) => m' (Format b e m)
genInf = formatEMS maxBound 0 <$> bit_
genNan = genQNan
genQNan = formatEMS maxBound
  <$> (setMSB <$> Gen.integral @m' @(BitArray m) (Range.linear 1 maxBound))
  <*> bit_
genSNan :: forall m' b e m . (H.MonadGen m', KnownNats b e m, KnownNat (m - 1), (m - 1) <= m) => m' (Format b e m)
genSNan = formatEMS maxBound <$> (upcast @(m - 1) @m <$> Gen.integral (Range.linear 1 maxBound)) <*> bit_
-- ^ TODO: clearMSB? Then don't need the m - 1 stuff.

-- * Compound

anyNativeWidth :: (H.MonadGen m') => (forall b e m . (KnownNats b e m, KnownNat (m - 1), (m - 1 <= m)) => m' (Format b e m)) -> m' AnyWidth
anyNativeWidth gen = Gen.choice [ F16 <$> gen, F32 <$> gen, F64 <$> gen ]

data AnyWidth
  = F16 Soft.Half
  | F32 Soft.Float
  | F64 Soft.Double
  deriving Show

withAnyWidth :: (forall b e m . (HasPrecisionLabel (Format b e m), KnownNat (m - 1)) => Format b e m -> x) -> AnyWidth -> x
withAnyWidth f = \case
  F16 a -> f a
  F32 a -> f a
  F64 a -> f a

softNativePair
  :: forall soft m' b e m
  . ( soft ~ Format b e m, KnownNats b e m
    , Storable soft
    , Storable (Native soft)
    , H.MonadGen m') => m' (soft, Native soft)
softNativePair = do
  soft :: soft <- genFloat
  return (soft, toNative soft)

toNative :: forall soft . (Storable soft, Storable (Native soft)) => soft -> Native soft
toNative soft = viaStorable @soft @(Native soft) soft

-- | Generate random decimal number as string, both negative and
-- positive and with or without the fraction part. E.g -9.2, 1, 8, 90842083.0
randomDecimalString
  :: forall t b e m m'
   . (t ~ Format b e m, KnownNat b, KnownNat e, KnownNat m, H.MonadGen m', HasPrecisionLabel t)
  => m' String
randomDecimalString = do
  addSign <- Gen.bool
  let minus x = '-' : show x
      plus x = show x
      sign :: Natural -> String
      sign x = (if addSign then "-" else "") <> show x

      maxNat = truncate (maxBound :: t)
      minNat = abs $ truncate (minBound :: t)

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

disable :: H.Property -> H.Property
disable _prop = H.property H.success
