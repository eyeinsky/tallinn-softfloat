module Data.Float where

import LocalPrelude

import Text.Read
import Data.Function (on)
import Data.Coerce
import Data.Proxy
import GHC.TypeLits
import Data.Kind
import Data.Char
import Data.Bits
import Data.Ratio
import Text.Printf

import Data.BitArray as BitArray


type Format :: Natural -> Natural -> Natural -> Type
data Format b q c where
  Finite
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


bias :: forall e . KnownNat e => BitArray e
bias = foldl' setBit 0 [0 .. (intVal @e) - 2]

unbiasedExponent :: forall s e m . Format s e m -> BitArray e
unbiasedExponent (Finite _s e _m) = e - bias @e

addBias :: forall e . BitArray e -> BitArray e
addBias (BitArray n) = BitArray (n + biasN)
  where BitArray biasN = bias @e

-- | Get the binary fraction of a float, i.e the 1/2 + 1/4 + 1/8 part
binaryFraction :: Format b e m -> Rational
binaryFraction (Finite _ _ (BitArray m :: BitArray m)) = foldl step 0 $ zip bitlist [1..]
  where
    step acc (bool, n) = if bool then acc + 1 % 2^n else acc
    bitlist = reverse $ map (\n -> testBit m n) [0 .. (fromIntegral (natVal @m Proxy) - 1)]

-- | significand = 1 + mantissa, idea from here: https://en.wikipedia.org/wiki/Significand
-- significand :: Format b e m -> BitArray.T -- TODO: BitArray (e + 1)
-- significand float@Finite{} = bitArrayInt (1 + mantissa float)
-- TODO: this was wrong, fix it

-- * Instances

instance Eq (Format b e m) where
  Finite s e m == Finite s' e' m' = s == s' && e == e' && m == m'

-- | Minimal an maximal non-infinity values.
instance (KnownNat b, KnownNat e, KnownNat m) => Bounded (Format b e m) where
  minBound = Finite I (maxBound - 1 :: BitArray e) (minBound :: BitArray m)
  maxBound = Finite O (maxBound - 1 :: BitArray e) (maxBound :: BitArray m)

instance (KnownNat b, KnownNat e, KnownNat m) => FiniteBits (Format b e m) where
  finiteBitSize _ = intVal @e + intVal @m + 1

instance (KnownNat b, KnownNat e, KnownNat m) => Bits (Format b e m) where
  Finite s1 e1 m1 .&. Finite s2 e2 m2 = Finite (s1 .&. s2) (e1 .&. e2) (m1 .&. m2)
  Finite s1 e1 m1 .|. Finite s2 e2 m2 = Finite (s1 .|. s2) (e1 .|. e2) (m1 .|. m2)
  Finite s1 e1 m1 `xor` Finite s2 e2 m2 = Finite (s1 `xor` s2) (e1 `xor` e2) (m1 `xor` m2)
  complement (Finite s e m) = Finite (complement s) (complement e) (complement m)
  shift f i = foldl' setBit zero $ newIndexes (+ i) f
  rotate f i = foldl' setBit zero $ newIndexes (\j -> mod (j + i) $ finiteBitSize f) f
  bitSize = finiteBitSize
  bitSizeMaybe = Just . finiteBitSize
  isSigned Finite{sign, exponent, mantissa} = sign == I

  testBit f@Finite{sign, exponent, mantissa} i
    | i < mantissaWidth = testBit mantissa i
    | i < lastBitIndex' - 1 = testBit exponent (i - mantissaWidth)
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
  f1@(Finite s1 e1 m1) * f2@(Finite s2 e2 m2) = trace (unlines
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
      e'shifts = length (drop (ix * 2) m'bitlist) - 1
      e'new = unbiasedExponent f1 + unbiasedExponent f2 + fromIntegral e'shifts
      e'new'biased = addBias e'new
      m'' = bitsToArrayBE $ tail $ m'bitlist

      float = Finite (s1 `xor` s2) e'new'biased m''

  negate f = f { sign = negate (sign f) }
  abs f = f { sign = O }
  signum f = (one @b) { sign = sign f }
  fromInteger i = let (_, (e, m)) = fromIntParts (fromInteger i) Nothing
    in Finite (boolBit $ i < 0) e m

hot' = let
  str = "2.25" :: String
  a = read str :: Binary32
  in do
  putStrLn $ str <> " string is parsed into " <> showFloatBits a
  p "exponent" $ bitArrayInt $ unbiasedExponent a
  p' "significand (1+)" $ "I : " <> show (bitListFinite (mantissa a))
  -- exporent 1100, multiplied I,O.O,I, O,O,O,O
  print $ a * a

fromIntegerBits :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Integer -> Format b e m
fromIntegerBits = fromBits @Integer

fromBits
  :: forall b' b e m . (Bits b', KnownNat b, KnownNat e, KnownNat m)
  => b' -> Format b e m
fromBits source = Finite
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
lxs label xs = label <> ": " <> show xs <> " (" <> show (length xs) <> ")"

p :: Show a => String -> a -> IO ()
p label a = putStrLn $ label <> ": " <> show a

p' :: String -> String -> IO ()
p' label str = putStrLn $ label <> ": " <> str

parseFloat
  :: forall b e m . (KnownNat b, KnownNat e, KnownNat m)
  => String -> ([String], (Format b e m, String))
parseFloat str = (
  [ l "input string" str ]
  <> debug <>
  [ l "float" $ showFloatBits float
  , l "float" $ float
  ]
  , (float, rest))
  where
    float = Finite sign e m
    (debug, (e, m)) = fromIntParts int maybeFracInt

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
  => Natural -> Maybe Natural -> ([String], (BitArray e, BitArray m))
fromIntParts int maybeFracInt =
  ( [ l "integer and fraction ints" (int, maybeFracInt)
    , l "int bits" $ intBits
    , l "target bit widths, e m" (intVal @e, intVal @m)
    , l "exponent" exponent
    ] <> xs
  , if
    | 0 <- int, Nothing <- maybeFracInt -> (0, 0)
    | 0 <- int, Just 0 <- maybeFracInt -> (0, 0)
    | otherwise -> (biasedExponent_, mantissa' :: BitArray m)
  )
  where
    intBits = bitList int
    exponent         = max (length intBits - 1) 0
    exponentBitList  = bitList exponent :: [Bit] -- big-endian
    exponentBitArray = bitsToArrayLE exponentBitList :: BitArray e
    biasedExponent   = addBias exponentBitArray :: BitArray e
    mantissaBits :: [Bit]
    biasedExponent_ :: BitArray e
    (mantissaBits, biasedExponent_, xs) = case maybeFracInt of
      Just fracInt -> let
        fracBits = fractionPartBits fracInt :: [Bit]
        (m, overflow) = roundBits (intVal @m + 1) (intBits <> fracBits) :: ([Bit], Bool)
        debug = [ lxs "fracBits" $ take 35 fracBits
                , l "round to N bits" (intVal @m)
                , lxs "m" $ take 35 m
                , l "overflow" overflow
                , l "exponent initial" biasedExponent
                , l "exponent +1" $ exponent + 1
                ]

        in if overflow
        then if maxBound == biasedExponent
             then error "overflow"
             else (m, biasedExponent + 1, debug)
        else (m, biasedExponent, debug)
      Nothing -> (intBits <> repeat O, biasedExponent, [])

    mantissa' = bitsToArrayBE $ drop 1 mantissaBits :: BitArray m

-- | Take fraction part digits as integer, convert it to bitlist. Big-endian.
fractionPartBits :: Natural -> [Bit]
fractionPartBits i = rationalToBits (i % (10^(length (show i))))

-- | big-endian
rationalToBits :: Ratio Natural -> [Bit]
rationalToBits i
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
mantissaBits (Finite s e m) = let mbits = showPosIntBits $ bitArrayInt m in (mbits, length mbits)

multiply :: forall b e m . Format b e m -> Format b e m -> Format b e m
multiply f1@(Finite s1 e1 m1) f2@(Finite s2 e2 m2) = Finite s e undefined
  where
    s = if s1 == s2 then O else I
    e = undefined -- m_exponent f1 f2 (bias @e)

-- * Show

instance Show (Format b e m) where
  show = fst . showDescribeFloat

showDescribeFloat :: forall b e m . Format b e m -> (String, String)
showDescribeFloat float@(Finite sign e m)
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

signalingBound :: forall b m . (KnownNat b, KnownNat m) => BitArray m
signalingBound = fromInteger $ (intVal @b)^(intVal @m - 1)

getPayload :: forall b e m . KnownNat (m - 1) => Format b e m -> Maybe (BitArray (m - 1))
getPayload (Finite _ _ (BitArray m)) = if not $ testBit m ix
  then Just $ BitArray $ clearBit m ix
  else Nothing
  where ix = intVal @m - 1

-- | Should this be in Fractional class?
floatToRational :: forall b e m . Format b e m -> Rational
floatToRational float@Finite{} = addSign (sign float) $ 2^^(exp - bitArrayInt (bias @e)) * (1 + binFrac)
  where
    exp = bitArrayInt $ exponent float -- :: Integer
    binFrac = binaryFraction float
    addSign :: Num a => Bit -> a -> a
    addSign sign b = case sign of
      O -> b
      I -> 0-b

describeFloat :: Format b e m -> String
describeFloat f = snd $ showDescribeFloat f

showFloatBits :: forall b e m . Format b e m -> String
showFloatBits (Finite sign e m) = intercalate "_" [[bitChar sign], bitStringFinite e, bitStringFinite m]

showFloatBits_ :: Format b e m -> String
showFloatBits_ = filter (/= '_') . showFloatBits

-- * Predefined

-- | 1: Mantissa is zero because it has an implicit 1 in
-- front. exponent is exactly bias, as then it will be 1 * 10_2^(bias - bias) = 1
one :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
one = Finite { sign = O, exponent = bias @e, mantissa = 0 }

zero :: forall b e m . (KnownNat b, KnownNat e, KnownNat m) => Format b e m
zero = Finite { sign = O, exponent = 0, mantissa = 0 }
