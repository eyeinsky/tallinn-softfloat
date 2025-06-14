{-# LANGUAGE TypeFamilies #-}
module Data.Float where

import LocalPrelude hiding (Float, Double)
import LocalPrelude qualified as Native

import Text.Read
import GHC.TypeLits
import Data.Kind
import Data.Char hiding (Format)
import Data.Bits
import Data.Word
import Data.Scientific qualified as Scientific

import Data.BitArray as BitArray hiding (multiply)
-- import Data.BitArray qualified as BitArray


type Format :: Natural -> Natural -> Natural -> Type
data Format b q c where
  Format
    :: (KnownNat b, KnownNat e, KnownNat m)
    => { sign :: Bit
       , exponent :: BitArray e
       , mantissa :: BitArray m
       } -> Format b e m

--                       base exponent mantissa                                  emax
type Half       = Format    2        5       10    -- half-precision               15
type Float      = Format    2        8       23    -- single-precision            127
type Double     = Format    2       11       52    -- double-precision           1023
type Binary128  = Format    2       15      112    -- quad-precision            16383
type Binary256  = Format    2       19      236    -- octuple-precision        262143


type family MatchingWord a where
  MatchingWord Half = Word16
  MatchingWord Float = Word32
  MatchingWord Double = Word64

  MatchingWord Native.Float = Word32
  MatchingWord Native.Double = Word64

-- * Bias

-- | Bias is always positive.
bias :: forall e . KnownNat e => BitArray e
bias = foldl' setBit 0 [0 .. (intVal @e) - 2]

unbias :: forall e . KnownNat e => BitArray e -> Integer
unbias e = toInteger $ e - (bias @e)

-- | Get unbiased exponent: take float's raw exponent and subtract its
-- bias. Result is Integer as it can be negative.
unbiasedExponent :: forall s e m . (KnownNat e, KnownNat m) => Format s e m -> Integer
unbiasedExponent = fst . exponentSignificand

data WidthResult a
  = Overflow Integer
  | Result a
  | Underflow Integer
  deriving Show

-- | Add bias to exponent @e@, indicate both under- or overflow
addBias_ :: forall e . KnownNat e => Integer -> WidthResult (BitArray e)
addBias_ e
  | eb <= 0 = Underflow $ minExponent @e - e -- absolute distance between given and the minimal exponent
  | eb > maxExponent' = Overflow $ eb - maxExponent'
  | otherwise = Result $ fromIntegral $ abs eb
  where
    eb = e + fromIntegral (bias @e) :: Integer
    maxExponent' = maxExponent @e :: Integer

-- | Add bias to exponent @e@. Nothing means underflow.
addBias :: forall e . KnownNat e => Integer -> BitArray e
addBias e = BitArray $ if e < 0
  then biasN - fromIntegral (abs e)
  else biasN + fromIntegral e
  where
    BitArray biasN = bias @e

-- | Get the binary fraction of a float, i.e the 1/2 + 1/4 + 1/8 part
asBinaryFraction :: BitArray m -> Rational
asBinaryFraction (BitArray m :: BitArray m) = foldl step 0 $ zip bitlist [(1 :: Integer)..]
  where
    step acc (bool, n) = if bool then acc + 1 % 2^n else acc
    bitlist = reverse $ map (\n -> testBit m n) [0 .. (intVal @m - 1)]

-- | significand = 1 + mantissa, idea from here: https://en.wikipedia.org/wiki/Significand
significand :: forall b e m . (KnownNat e, KnownNat m) => Format b e m -> Natural
significand = snd . exponentSignificand

exponentSignificand :: forall b e m . (KnownNat e, KnownNat m) => Format b e m -> (Integer, Natural)
exponentSignificand Format{exponent, mantissa} = if exponent == 0
  then (1 - bias', bitArrayInt mantissa) -- subnormal
  else (toInteger exponent - bias', setBit (bitArrayInt mantissa) (intVal @m)) -- normal
  where
    bias' = toInteger (bias @e)

-- * Instances

instance Eq (Format b e m) where
  Format s e m == Format s' e' m' = s == s' && e == e' && m == m'

-- | Minimal an maximal non-infinity values. Exponent for both is
-- one-less than all-ones exponent, as otherwise it will be infinity
-- or nan (depending on mantissa value).

maxExpBiased :: forall w . KnownNat w => BitArray w
maxExpBiased = (maxBound :: BitArray w) - 1

maxExponent :: forall e a . (KnownNat e, Num a) => a
maxExponent = fromIntegral (maxExpBiased :: BitArray e)

minExpBiased :: forall e . KnownNat e => BitArray e
minExpBiased = 1

minExponent :: forall e a . (KnownNat e, Num a) => a
minExponent = 1 - fromIntegral (bias @e)

instance (KnownNat b, KnownNat e, KnownNat m) => Bounded (Format b e m) where
  minBound = Format I maxExpBiased (maxBound :: BitArray m)
  maxBound = Format O maxExpBiased (maxBound :: BitArray m)

instance (KnownNat b, KnownNat e, KnownNat m) => FiniteBits (Format b e m) where
  finiteBitSize _ = intVal @e + intVal @m + 1

instance (KnownNat b, KnownNat e, KnownNat m) => Bits (Format b e m) where
  Format s1 e1 m1 .&. Format s2 e2 m2 = Format (s1 .&. s2) (e1 .&. e2) (m1 .&. m2)
  Format s1 e1 m1 .|. Format s2 e2 m2 = Format (s1 .|. s2) (e1 .|. e2) (m1 .|. m2)
  Format s1 e1 m1 `xor` Format s2 e2 m2 = Format (s1 `xor` s2) (e1 `xor` e2) (m1 `xor` m2)
  complement (Format s e m) = Format (complement s) (complement e) (complement m)

  shift f i = foldl' setBit zero $ newIndexes (+ i) f

  rotate f i = foldl' setBit zero $ newIndexes (\j -> mod (j + i) $ finiteBitSize f) f
  bitSize = finiteBitSize
  bitSizeMaybe = Just . finiteBitSize
  isSigned Format{sign} = sign == I
  popCount (Format s e m) = popCount e + popCount m + (case s of I -> 1; O -> 0)

  testBit f@Format{sign, exponent, mantissa} i
    | i < mantissaWidth = testBit mantissa i
    | i < lastBitIndex' = testBit exponent (i - mantissaWidth)
    | i == lastBitIndex' = sign == I
    | otherwise = False
    where
      mantissaWidth = intVal @m
      lastBitIndex' = lastBitIndex f

  bit i
    | i < mantissaWidth       = zero' { mantissa = bit i }
    | i' < exponentWidth      = zero' { exponent = bit i' }
    | 0 <- i' - exponentWidth = zero' { sign = I }
    | otherwise               = zero'
    where
      zero' = zero @b @_ @m
      mantissaWidth = intVal @m
      exponentWidth = intVal @e
      i' = i - mantissaWidth

instance FiniteBinary Half where
  type Width (Format 2 5 10) = 16
instance FiniteBinary Float where
  type Width (Format 2 8 23) = 32
instance FiniteBinary Double where
  type Width (Format 2 11 52) = 64
instance FiniteBinary Binary128 where
  type Width (Format 2 15 112) = 128
instance FiniteBinary Binary256 where
  type Width (Format 2 19 236) = 256

-- | Read a float from a value having a binary representation, i.e, a @Bits@ instance.
-- TODO add tests
fromBits_
  :: forall bits b e m . (Bits bits, KnownNat b, KnownNat e, KnownNat m)
  => bits -> Format b e m
fromBits_ source = Format
  { sign = if testBit source (mw + ew) then I else O
  , exponent = integerBits source mw (mw + ew)
  , mantissa = integerBits source 0 mw
  }
  where
    ew = intVal @e
    mw = intVal @m
    integerBits :: (KnownNat width) => bits -> Int -> Int -> BitArray width
    integerBits source from to = BitArray $ foldl' step 0 mapping
      where
        step acc (ix0, ix1) = if testBit source ix0 then setBit acc ix1 else acc
        mapping :: [(Int, Int)]
        mapping = zip [from .. (to - 1) ] [0..]

toBits :: (FiniteBits f, Bits (MatchingWord f)) => f -> MatchingWord f
toBits f = go 0 zeroBits
  where
    go ix v = if ix == finiteBitSize f
      then v
      else go (ix + 1) $ if testBit f ix then setBit v ix else v

instance (KnownNat b, KnownNat e, KnownNat m) => Num (Format b e m) where
  (+) = u -- :: a -> a -> a
  (-) = u --  :: a -> a -> a
  f1 * f2 = snd $ (multiply @b @e @m) f1 f2
  negate f = f { sign = negate (sign f) }
  abs f = f { sign = O }
  signum f = (one @b) { sign = sign f }
  fromInteger i = let (_, (e, m)) = fromIntParts (fromInteger i) 0
    in Format (boolBit $ i < 0) e m

l :: Show a => String -> a -> String
l label a = label <> ": " <> show a

lxs :: Show a => String -> Int -> [a] -> String
lxs label cap xs = let
    xs' = take cap xs
    cappedMsg = if length xs' == cap then ", capped" else ""
    value = show xs' <> " (" <> show (length xs') <> cappedMsg <> ")"
  in label <> ": " <> value

-- FIXME this doesn't work fractions with zeroes in front of of the fraction part, i.e 0.0625 parses to 0.625
parseFloat
  :: forall b e m . (KnownNat b, KnownNat e, KnownNat m)
  => String -> ([String], (Format b e m, String))
parseFloat str = (
  [ l "input string" str ]
  <> debug <>
  [ l "float bits" $ showFloatBits float
  , l "float" $ float
  ]
  , (float, rest))
  where
    float = Format sign e m
    (debug, (e, m)) = fromIntParts int $ fromMaybe 0 maybeFracInt

    -- | Parse string to integer and fraction parts
    (sign :: Bit, int :: Natural, maybeFracInt :: Maybe Natural, rest :: String) = let
      (minus, str') = span (== '-') str
      (intDigits, rest0) = span isDigit str'
      in case intDigits of
        "" -> error "No int digits"
        _ -> let
          (maybeFrac, rest2) = case rest0 of
            '.' : rest1 -> let (fracDigits, rest3) = span isDigit rest1
                           in (readMaybe fracDigits, rest3)
            _noFrac -> (Nothing, rest0)
          in (boolBit $ minus == "-", read intDigits, maybeFrac, rest2)

fromIntParts
  :: forall e m . (KnownNat e, KnownNat m)
  => Natural -> Natural -> ([String], (BitArray e, BitArray m))
fromIntParts 0 0 = (["fromIntParts (0, 0)"], (0, 0))
fromIntParts int fracInt = (debug, (biasedExponent_, bitsToArrayBE mantissaBits :: BitArray m))
  where
    intBits = bitListIntegral int
    fracBits = fractionPartBits fracInt :: [Bit]
    (mantissa, exp) = normalizeMantissa intBits fracBits
    biasedExp = addBias exp :: BitArray e
    (mantissa', extraDigit) = roundBits (intVal @m + 1) mantissa
    biasedExp' = if extraDigit then biasedExp + 1 else biasedExp

    debug =
      [ "<maybeFracInt>"
      , lxs "int bits" 70 intBits
      , lxs "fracBits bits" 70 fracBits
      , lxs "normalizeMantissa" 70 mantissa
      , l "exp" exp
      , lxs "rounded mantissa" 70 mantissa'
      , l "exp, biased" biasedExp'
      , l "biased exponent == maxExpBiased" ((biasedExp', maxExpBiased :: BitArray e), (biasedExp' == maxExpBiased))
      , l "extra digit" extraDigit
      , "</maybeFracInt>"
      ]

    (mantissaBits :: [Bit], biasedExponent_ :: BitArray e) = if biasedExp' > maxExpBiased -- the only higher value is all-ones
      then (replicate (intVal @m) 0, maxBound) -- infinity
      else (drop 1 mantissa', biasedExp')      -- drop 1: leave leading bit implicit

-- | Take integer bits and fraction bits and produce mantissa bits
-- and an unbiased exponent.
normalizeMantissa :: [Bit] -> [Bit] -> ([Bit], Integer)
normalizeMantissa intBitsBE_ fracBitsBE
  | null intBitsBE = dropCountZeroes 0 fracBitsBE
  | otherwise =
    ( intBitsBE <> fracBitsBE
    , max (toInteger $ length intBitsBE - 1) 0)
  where
    intBitsBE = dropWhile (== O) intBitsBE_
    dropCountZeroes n xs = case xs of
      b : bs -> case b of
        I -> (xs, n - 1)
        O -> dropCountZeroes (n - 1) bs
      [] -> ([], 0)

-- | Take fraction part digits as integer, convert it to bitlist. Big-endian.
fractionPartBits :: Natural -> [Bit]
fractionPartBits i = rationalToBits (i % 10^digitCount)
  where
    digitCount = length $ show i

-- | big-endian
rationalToBits :: Ratio Natural -> [Bit]
rationalToBits i
  | i == 0 = []
  | i2 < 1 = O : recurse i2
  | i2 > 1 = 1 : recurse (i2 - 1)
  | i2 == 1 = 1 : []
  | otherwise = error "this should never happen"
  where
    i2 = i * 2
    recurse = rationalToBits

instance (KnownNat b, KnownNat e, KnownNat m) => Read (Format b e m) where
  readsPrec _n str = [snd $ parseFloat str]

instance (KnownNat b, KnownNat e, KnownNat m) => Fractional (Format b e m) where
  (/) = u
  recip = u
  fromRational r = f
    where
      -- TODO stopgap that goes through scientific and string, replace with a real parser
      sci = fromRational r :: Scientific.Scientific
      str = Scientific.formatScientific Scientific.Fixed Nothing sci
      (_, (f, _)) = parseFloat str

mantissaBits :: Format b q c -> (String, Int)
mantissaBits (Format _s _e m) = let mbits = showPosIntBits $ bitArrayInt m in (mbits, length mbits)

multiply :: forall b e m . Format b e m -> Format b e m -> ([String],  Format b e m)
multiply f1@(Format sign1 _ _m1) f2@(Format sign2 _ _m2)
  | isNan f1 || isNan f2 = ([], addSign nan)                       -- nan * _ = nan
  | isInf f1 && f2 == 0 || isInf f2 && f1 == 0 = ([], addSign nan) -- 0 * inf = nan
  | isZero f1 || isZero f2 = ([], addSign 0)                       -- 0 * _   = 0
  | isInf f1 || isInf f2 = ([], addSign inf)                       -- inf * _ = inf
  | otherwise = (debug, addSign float)
  where
    addSign f = f{sign}
    sign = sign1 `xor` sign2
    ix = intVal @m :: Integer

    s0 = significand f1 * significand f2 :: Natural
    subnormalS0 = not $ testBit s0 (intVal @m * 2) && not (testBit s0 (intVal @m * 2 + 1)) -- no 1. nor 10. for s0

    e0 = unbiasedExponent f1 + unbiasedExponent f2 :: Integer
    e1 = addBias_ @e e0 :: WidthResult (BitArray e)

    float, float' :: Format b e m
    float' = zero
    (float, debug') = if subnormalS0

      then let
          hsb = fromIntegral $ highestSetBit s0 -- this many steps to zero
          dNormal = intVal @m * 2 - hsb -- this many steps to get to normal
          e0' = e0 - dNormal
          e1' = addBias_ @e e0'

          (float, debug') = case e1' of
            Underflow exponentUnderflow -> let

              in
              (zero, [])
            _ -> (zero, [])

          in (float,
              [ "\nSUBNORMAL"
              , l "hsb" hsb
              , l "dNormal" dNormal
              , l "e0'" e0'
              , l "e1'" e1'
              ] <> debug'
             )


      else case e1 of
        Overflow{} -> (Format sign maxBound 0, ["OVERFLOW"]) -- exponent overflow means infinity
        Underflow exponentUnderflow ->
          let
            roundTo = fromIntegral $ exponentUnderflow + ix -- round more to the amount of underflow
            debug' =
              [ "\nEXPONENT UNDERFLOW"
              , l "roundTo" roundTo
              , l "m" $ BitArray @24 n
              , l "m" m
              , l "roundingOverflow" roundingOverflow
              ]
            n = roundEven roundTo s0 :: Natural
            roundingOverflow = testBit n (intVal @m)
            m = BitArray n
            float = if exponentUnderflow == 1 && roundingOverflow -- roundingOverflow can only improve exponent by an amount of 1
              then Format sign 1 (clearBit m (intVal @m))
              else Format sign 0 m

          in (float, debug')

        Result e -> let
            hsb = highestSetBit s0
            ix2 = intVal @m * 2
            sigMultOverflow = hsb /= ix2
            roundTo = if sigMultOverflow then ix + 1 else ix
            s1 = roundEven (fromIntegral roundTo) s0
            roundingOverflow = testBit s1 (intVal @m + 1)

            m = BitArray (clearBit s1 (intVal @m))
            float = if roundingOverflow || sigMultOverflow
              then Format sign (e + 1) m
              else Format sign e m

          in (float,
              [ "\nEXPONENT RESULT " <> show e
              , l "highestSetBit" hsb
              , l "roundTo (sigMultOverflow)" (roundTo, sigMultOverflow)
              , l "s1 (rounded to roundTo)" $ prettyBinFrac (intVal @m) s1
              , l "roundingOverflow" roundingOverflow
              ])

    debug =
      [ "s0: " <> prettyBinFrac (intVal @m * 2) s0 <> " subnormalS0: " <> show subnormalS0
      , "e0, unbiased: " <> unwords [show e0, "=", show (unbiasedExponent f1), "+", show (unbiasedExponent f2) <> ", min/max " <> show (minExponent @e) <> "/" <> show (maxExponent @e)]
      , l "e1, bias result" e1
      ] <> debug'

highestSetBit :: Natural -> Int
highestSetBit n = floor $ logBase (2 :: Native.Double) $ fromIntegral n

divide :: (KnownNat b, KnownNat e, KnownNat m) => Format b e m -> Format b e m -> Format b e m
divide _a b
  | 0 <- b = inf -- plus sign from either
  | otherwise = u

-- * Show

instance Show (Format b e m) where
  show = fst . showDescribeFloat

showDescribeFloat :: forall b e m . Format b e m -> (String, String)
showDescribeFloat float@(Format sign e m)
  | 0 <- e = case m of
      -- zero: exponent and mantiassa are zeroes
      0 -> (s <> "0.0", ws [signWord, Just "zero"])
      -- all-zero exponent, but non-zero mantissa
      _ -> (viaRational, "subnormal")
  | maxBound == e  = case m of
      -- infinity: exponent all ones, mantissa all zeroes
      0 -> (s <> "inf", ws [signWord, Just "infinity"])
       -- NaN: exponent is all ones, mantissa not all zeroes; mantissa greater than signalingBound is a signaling NaN
      _ -> (s <> sg <> "nan", ws [signWord, siganling, Just "nan"])
  | otherwise      = (viaRational, "normal")
  where
    ws = unwords . catMaybes
    s = case sign of I -> "-"; O -> ""
    viaRational = show @Native.Double $ fromRational $ floatToRational float :: String

    signWord = Just $ case sign of O -> "positive"; I -> "negative"
    (siganling, sg) = if testBit m (intVal @m - 1) then (Nothing, "") else (Just "signaling", "s")

describeFloat :: Format b e m -> String
describeFloat f = snd $ showDescribeFloat f

showFloatBits :: forall b e m . Format b e m -> String
showFloatBits (Format sign e m) = intercalate "_" [[bitChar sign], bitStringFinite e, bitStringFinite m]

showFloatBits_ :: Format b e m -> String
showFloatBits_ = filter (/= '_') . showFloatBits

-- * Unsorted

-- | Should this be in Fractional class?
floatToRational :: forall b e m . Format b e m -> Rational
floatToRational f@(Format sign exponent mantissa) = case exponent of
  -- subnormal
  0 -> addSign sign $ 2^^(unbiasedExponent f) * asBinaryFraction mantissa
  -- normal
  _ -> addSign sign $ 2^^(unbiasedExponent f) * rationalMantissa mantissa
  where
    addSign :: Num a => Bit -> a -> a
    addSign sign = case sign of
      O -> id
      I -> negate

rationalMantissa :: BitArray w -> Rational
rationalMantissa m = 1 + asBinaryFraction m

floatInt :: Format b e m -> Integer
floatInt f = div n d
  where
    r = floatToRational f
    n = numerator r
    d = denominator r

-- * NaN signaling

signalingBound :: forall b m . (KnownNat b, KnownNat m) => BitArray m
signalingBound = fromInteger $ ((intVal @b :: Integer)^(intVal @m - 1 :: Integer))

snanPayload :: forall b e m . KnownNat (m - 1) => Format b e m -> Maybe (BitArray (m - 1))
snanPayload (Format _ _ (BitArray m)) = if not $ testBit m ix
  then Just $ BitArray $ clearBit m ix
  else Nothing
  where ix = intVal @m - 1

-- * Predefined

-- | 1: Mantissa is zero because it has an implicit 1 in
-- front. exponent is exactly bias, as then it will be 1 * 10_2^(bias - bias) = 1
one :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
one = Format { sign = O, exponent = bias @e, mantissa = 0 }

zero :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
zero = Format { sign = O, exponent = 0, mantissa = 0 }

-- | Positive infinity: exponent is all-ones, mantissa is all-zeroes.
inf :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
inf = Format { sign = O, exponent = maxBound, mantissa = 0 }

-- | NaN is like infinity, but with a non-zero mantissa.
nan, qnan :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
nan = (inf @b @e @m) { mantissa = setBit 0 (intVal @m - 1) }
qnan = nan

-- | Signaling NaN has most significant bit zero, the rest holds argument data.
snan :: forall b e m m' . (KnownNat b, KnownNat e, KnownNat m, KnownNat m', m' <= m - 1) => BitArray m' -> Format b e m
snan (BitArray data_) = (inf @b @e @m) { mantissa = BitArray data_ }

-- * Predicates

isNan :: Format b e m -> Bool
isNan Format{exponent, mantissa} = exponent == maxBound && mantissa /= 0

isInf :: Format b e m -> Bool
isInf Format{exponent, mantissa} = exponent == maxBound && mantissa == 0

isSubnormal :: Format b e m -> Bool
isSubnormal Format{exponent} = exponent == 0

isZero :: Format b e m -> Bool
isZero = \case
  Format _ 0 0 -> True
  _ -> False
