module Data.Float where

import LocalPrelude hiding (Float, Double)

import Text.Read
import Data.Function (on)
import Data.Coerce
import Data.Proxy
import GHC.TypeLits
import Data.Kind
import Data.Char hiding (Format)
import Data.Bits
import Data.Ratio
import Text.Printf

import Data.BitArray as BitArray


type Format :: Natural -> Natural -> Natural -> Type
data Format b q c where
  Format
    :: (KnownNat b, KnownNat e, KnownNat m)
    => { sign :: Bit
       , exponent :: BitArray e
       , mantissa :: BitArray m
       } -> Format b e m

--                       base exponent mantissa                                  emax
type Binary16   = Format    2        5       10    -- half-precision               15
type Binary32   = Format    2        8       23    -- single-precision            127
type Binary64   = Format    2       11       52    -- double-precision           1023
type Binary128  = Format    2       15      112    -- quad-precision            16383
type Binary256  = Format    2       19      236    -- octuple-precision        262143

type Half = Binary16
type Float = Binary32
type Double = Binary64

-- * Bias

-- | Bias is always positive.
bias :: forall e . KnownNat e => BitArray e
bias = foldl' setBit 0 [0 .. (intVal @e) - 2]

-- | Get unbiased exponent: take float's raw exponent and subtract its
-- bias. Result is Integer as it can be negative.
unbiasedExponent :: forall s e m . Format s e m -> Integer
unbiasedExponent (Format _s e _m) = toInteger e - toInteger (bias @e)

addBias' :: forall e . BitArray e -> BitArray e
addBias' (BitArray n) = BitArray (n + biasN)
  where BitArray biasN = bias @e

addBias :: forall ew . KnownNat ew => Integer -> BitArray ew
addBias e = BitArray $ if e < 0
  then biasN - fromIntegral (abs e)
  else biasN + fromIntegral e
  where
    BitArray biasN = bias @ew

-- | Get the binary fraction of a float, i.e the 1/2 + 1/4 + 1/8 part
asBinaryFraction :: BitArray m -> Rational
asBinaryFraction (BitArray m :: BitArray m) = foldl step 0 $ zip bitlist [1..]
  where
    step acc (bool, n) = if bool then acc + 1 % 2^n else acc
    bitlist = reverse $ map (\n -> testBit m n) [0 .. (fromIntegral (natVal @m Proxy) - 1)]

-- | significand = 1 + mantissa, idea from here: https://en.wikipedia.org/wiki/Significand
-- significand :: Format b e m -> BitArray.T -- TODO: BitArray (e + 1)
-- significand float@Format{} = bitArrayInt (1 + mantissa float)
-- TODO: this was wrong, fix it

-- * Instances

instance Eq (Format b e m) where
  Format s e m == Format s' e' m' = s == s' && e == e' && m == m'

-- | Minimal an maximal non-infinity values. Exponent for both is
-- one-less than all-ones exponent, as otherwise it will be infinity
-- or nan (depending on mantissa value).

maxExponent :: forall w . KnownNat w => BitArray w
maxExponent = (maxBound :: BitArray w) - 1
instance (KnownNat b, KnownNat e, KnownNat m) => Bounded (Format b e m) where
  minBound = Format I maxExponent (maxBound :: BitArray m)
  maxBound = Format O maxExponent (maxBound :: BitArray m)

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
  isSigned Format{sign, exponent, mantissa} = sign == I

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

instance (KnownNat b, KnownNat e, KnownNat m) => Num (Format b e m) where
  (+) = u -- :: a -> a -> a
  (-) = u --  :: a -> a -> a
  f1@(Format s1 e1 m1) * f2@(Format s2 e2 m2) = trace (unlines
    [ ""
    , l "e1, unbiased" $ unbiasedExponent f1
    , l "e2, unbiased" $ unbiasedExponent f2
    , l "m1'" m1'
    , l "m2'" m2'
    , l "m1+1" m1''
    , l "m2+1" m2''
    , l "m'" m'
    , l "m'" $ (BitArray m' :: BitArray 8)
    , l "m'bitlist" $ m'bitlist
    , l "m'bitlist" $ reverse $ drop (ix * 2) $ reverse m'bitlist
    , l "e'shifts" $ e'shifts
    , l "e'new" e'new
    , l "e'new'biased" e'new'biased
    , "float: " <> showFloatBits float
    ]) $
    float
    where
      BitArray m1' = m1
      BitArray m2' = m2
      ix = intVal @m
      m1'' = setBit m1' ix
      m2'' = setBit m2' ix
      m' = m1'' * m2''
      m'bitlist = bitList m'

      e'shifts = toInteger $ length (drop (ix * 2) m'bitlist) - 1

      e'new = unbiasedExponent f1 + unbiasedExponent f2 + e'shifts

      e'new'biased = addBias e'new
      m'' = bitsToArrayBE $ tail $ m'bitlist

      float = Format (s1 `xor` s2) e'new'biased m''

  negate f = f { sign = negate (sign f) }
  abs f = f { sign = O }
  signum f = (one @b) { sign = sign f }
  fromInteger i = let (_, (e, m)) = fromIntParts (fromInteger i) 0
    in Format (boolBit $ i < 0) e m

fromIntegerBits :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Integer -> Format b e m
fromIntegerBits = fromBits @Integer

fromBits
  :: forall b' b e m . (Bits b', KnownNat b, KnownNat e, KnownNat m)
  => b' -> Format b e m
fromBits source = Format
  { sign = if testBit source (mw + ew) then I else O
  , exponent = integerBits source mw (mw + ew)
  , mantissa = integerBits source 0 mw
  }
  where
    ew = intVal @e
    mw = intVal @m
    integerBits :: (Bits t, KnownNat width) => t -> Int -> Int -> BitArray width
    integerBits source from to = BitArray $ foldl' step 0 mapping
      where
        step acc (ix0, ix1) = if testBit source ix0 then setBit acc ix1 else acc
        mapping :: [(Int, Int)]
        mapping = zip [from .. (to - 1) ] [0..]

l label a = label <> ": " <> show a
lxs label cap xs = let
    xs' = take cap xs
    cappedMsg = if length xs' == cap then ", capped" else ""
    value = show xs' <> " (" <> show (length xs') <> cappedMsg <> ")"
  in label <> ": " <> value

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
    intBits = bitList int
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
      , l "biased exponent == maxExponent" ((biasedExp', maxExponent :: BitArray e), (biasedExp' == maxExponent))
      , l "extra digit" extraDigit
      , "</maybeFracInt>"
      ]

    (mantissaBits :: [Bit], biasedExponent_ :: BitArray e) = if biasedExp' > maxExponent -- the only higher value is all-ones
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
  where
    i2 = i * 2
    recurse = rationalToBits

instance (KnownNat b, KnownNat e, KnownNat m) => Read (Format b e m) where
  readsPrec n str = [snd $ parseFloat str]

instance (KnownNat b, KnownNat e, KnownNat m) => Fractional (Format b e m) where
  (/) = u
  recip = u
  fromRational = u

mantissaBits :: Format b q c -> (String, Int)
mantissaBits (Format s e m) = let mbits = showPosIntBits $ bitArrayInt m in (mbits, length mbits)

multiply :: forall b e m . Format b e m -> Format b e m -> Format b e m
multiply f1@(Format s1 e1 m1) f2@(Format s2 e2 m2) = Format s e undefined
  where
    s = if s1 == s2 then O else I
    e = undefined -- m_exponent f1 f2 (bias @e)

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
       -- NaN: exponent is all ones, mantissa not all zeroes; mantussa greater than signalingBound is a signaling NaN
      _ -> (s <> sg <> "nan", ws [signWord, siganling, Just "nan"])
  | otherwise      = (viaRational, "regular float: " <> show float)
  where
    ws = unwords . catMaybes
    s = case sign of I -> "-"; O -> ""
    viaRational = show $ fromRational $ floatToRational float :: String

    signWord = Just $ case sign of O -> "positive"; I -> "negative"
    (siganling, sg) = if testBit m (intVal @m - 1) then (Nothing, "") else (Just "signaling", "s")

-- | Should this be in Fractional class?
floatToRational :: forall b e m . Format b e m -> Rational
floatToRational f@(Format sign exponent mantissa) =
  addSign sign $ 2^^(unbiasedExponent f) * rationalMantissa mantissa
  where
    addSign :: Num a => Bit -> a -> a
    addSign sign b = case sign of
      O -> b
      I -> 0-b

rationalMantissa :: BitArray w -> Rational
rationalMantissa m = 1 + asBinaryFraction m

floatInt :: Format b e m -> Integer
floatInt f = div n d
  where
    r = floatToRational f
    n = numerator r
    d = denominator r

-- *

signalingBound :: forall b m . (KnownNat b, KnownNat m) => BitArray m
signalingBound = fromInteger $ (intVal @b)^(intVal @m - 1)

getPayload :: forall b e m . KnownNat (m - 1) => Format b e m -> Maybe (BitArray (m - 1))
getPayload (Format _ _ (BitArray m)) = if not $ testBit m ix
  then Just $ BitArray $ clearBit m ix
  else Nothing
  where ix = intVal @m - 1

describeFloat :: Format b e m -> String
describeFloat f = snd $ showDescribeFloat f

showFloatBits :: forall b e m . Format b e m -> String
showFloatBits (Format sign e m) = intercalate "_" [[bitChar sign], bitStringFinite e, bitStringFinite m]

showFloatBits_ :: Format b e m -> String
showFloatBits_ = filter (/= '_') . showFloatBits

-- * Predefined

-- | 1: Mantissa is zero because it has an implicit 1 in
-- front. exponent is exactly bias, as then it will be 1 * 10_2^(bias - bias) = 1
one :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
one = Format { sign = O, exponent = bias @e, mantissa = 0 }

zero :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
zero = Format { sign = O, exponent = 0, mantissa = 0 }
