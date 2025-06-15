{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Data.Bit where

import Prelude
import Data.Bits
import Data.List
import Numeric.Natural

import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Data.Word
import System.IO.Unsafe
import Debug.Trace
import Data.Proxy
import GHC.TypeLits
import Data.Kind
import Data.Int

data Bit = O | I deriving (Eq, Show, Enum)

instance Bits Bit where
  I .&. I = I
  _ .&. _ = O

  I .|. _ = I
  _ .|. I = I
  _ .|. _ = O

  a `xor` b = if a /= b then I else O

  complement = \case I -> O; O -> I
  shift x i = case i of 0 -> x; _ -> O
  rotate x _ = x
  bitSize _ = 1
  bitSizeMaybe _ = Just 1
  isSigned _ = False
  testBit x i = case i of 0 -> x == I; _ -> False
  bit = \case 0 -> I; _ -> O
  popCount = \case I -> 1; O -> 0

instance Num Bit where
  (+) = xor
  (-) = xor
  (*) = (.&.)
  negate = \case O -> I; I -> O
  abs b = b
  signum b = b
  fromInteger i = boolBit $ testBit i 0

getBit :: Bits a => a -> Int -> Bit
getBit a i = boolBit $ testBit a i

boolBit :: Bool -> Bit
boolBit = \case True -> I; False -> O

bitChar :: Bit -> Char
bitChar = \case O -> '0'; I -> '1'

-- * Bit list

-- | List of bits, infinite, little-endian.
bitList :: Bits a => a -> [Bit]
bitList a = map (getBit a) [0..]

-- | Calculate a bitlist for integrals by capping the list when
-- argument is reached. Big-endian, starts always with a @I@, possibly
-- infinite.
bitListIntegral :: forall a . (Bits a, Integral a) => a -> [Bit]
bitListIntegral a = go ([], 0) $ zip [0..] $ bitList a
  where
    go :: ([Bit], a) -> [(Int, Bit)] -> [Bit]
    go (acc, sum) ((i, bit) : rest) =
      if sum == a
      then acc
      else case bit of
        I -> let sum' = sum + (2^i)
             in go (bit : acc, sum') rest
        O -> go (bit : acc, sum) rest
    go _ _ = error "TODO"

-- | List of bits for argument, big-endian.
bitListFinite :: FiniteBits a => a -> [Bit]
bitListFinite a = map (getBit a) [l, l - 1 .. 0] where l = lastBitIndex a

-- | List of bits for argument, little-endian.
bitListFiniteLE :: FiniteBits a => a -> [Bit]
bitListFiniteLE a = map (getBit a) [0..lastBitIndex a]

-- | Round bitlist to @n@ digits. The returned Bool indicates whether
-- by rounding up an additional 1 bit was added as the most
-- significant bit. Input/output are big-endian.
roundBits :: Int -> [Bit] -> ([Bit], Bool)
roundBits n bits = let
    (a, overflow) = splitAt n bits
    a' = reverse a -- little-endian
  in case overflow of
      -- first overflow bit is zero or there are no overflow bits => truncate
      [] -> (a, False)
      O : _ -> (a, False)
      I : rest -> if all (== O) rest
        then case a' of        -- it's a tie
          I : _ -> ceiling a'  -- remainder is odd => round up
          O : _ -> (a, False)  -- remainder is even => round down
          []    -> (a, False)  -- same => round down
        else ceiling a'        -- round up
  where
    ceiling a = let (x, y) = add1 a in (reverse x, y)

-- | Add 1 to little-endian bit list. Second member signifies whether
-- an extra digit was added.
add1 :: [Bit] -> ([Bit], Bool)
add1 bits' = case bits' of
  O : rest -> (I : rest, False)
  I : rest -> let (bs, o) = add1 rest in (O : bs, o)
  [] -> ([I], True)

-- * Data.Bits.Extra

-- | Return value with last @n@ bits from argument.
suffix :: Bits a => Int -> a -> a
suffix n a = foldl' step zeroBits [0 .. (n - 1)]
  where step acc i = if testBit a i then setBit acc i else acc

-- | Top bits of @a@ as [Bool], reversed
topBits :: FiniteBits a => a -> Int -> [Bool]
topBits a n = foldl' (\acc i -> testBit a i : acc) [] $ take n [max, max - 1 .. 0]
  where
    max = finiteBitSize a - 1

lastBitIndex :: FiniteBits a => a -> Int
lastBitIndex a = finiteBitSize a - 1

newIndexes :: FiniteBits a => (Int -> Int) -> a -> [Int]
newIndexes op a = map fst $ filter (\(j, b) -> j <= lastBitIndex' && b) $ map (\j -> (op j, testBit a j)) [0 .. lastBitIndex']
  where
    lastBitIndex' = lastBitIndex a

toBitBoolListN :: Bits a => a -> Int -> [Bool]
toBitBoolListN a max = map (\i -> testBit a i) [max, max - 1 .. 0]

binaryNatural :: forall a . FiniteBits a => a -> Natural
binaryNatural a = foldl' step zeroBits [0 .. lastBitIndex a]
  where step acc i = if testBit a i then setBit acc i else acc

-- ** Pretty

boolBitChar :: Bool -> Char
boolBitChar = \case
  True -> '1'
  False -> '0'

bitStringFinite :: FiniteBits a => a -> String
bitStringFinite = map bitChar . bitListFinite

-- | Print value having a FiniteBits instance as binary literal, e.g 0b0110..
binaryLiteral :: FiniteBits a => a -> String
binaryLiteral a = "0b" <> map bitChar (bitListFinite a)

binaryLiteralChunked :: (Bits a, Integral a) => [Int] -> a -> String
binaryLiteralChunked ixs a = go ixs (dropWhile (== O) $ bitListIntegral a)
  where
    go xs bs = case xs of
      x : xs' -> let
        (bs0, bs1) = splitAt x bs
        tail' = if null bs1 then "" else "_" <> go xs' bs1
        in map bitChar bs0 <> tail'
      [] -> map bitChar bs

prettyBinFrac :: forall a . (Bits a) => Int -> a -> String
prettyBinFrac n a = prettyBin (shiftR a n) <> "." <> frac
  where
    frac = reverse $ map bitChar $ take n $ bitList $ suffix n a

prettyBin :: Bits a => a -> String
prettyBin a = reverse $ prettyBinLE a

prettyBinLE :: Bits a => a -> String
prettyBinLE rest = boolBitChar (testBit rest 0) : let
  rest' = shiftR rest 1 -- TODO: how is popCount available for non-FinteBits types
  in if popCount rest' == 0
  then []
  else prettyBinLE rest'

-- TODO make result BitArray as it shows better?
bitsNatural :: forall a . Bits a => a -> Natural
bitsNatural a = go a zeroBits 0
  where
    go :: a -> Natural -> Int -> Natural
    go rest acc ix
      | popCount rest == 0 = acc
      | testBit rest 0 = go (shiftR rest 1) (setBit acc ix) (ix + 1)
      | otherwise = go (shiftR rest 1) acc (ix + 1)

-- ** Rounding

-- | Round off @n@ bits from right.
roundEven :: forall a . (Bits a, Num a, Ord a) => Int -> a -> a
roundEven 0 a = a
roundEven n a = if
  -- first remainder bit is 0: truncate
  | not r -> t0
  -- first remainder bit is 1 and remainder is more: round up
  | suffix n a > bit i -> t1
  -- it's a tie and it's odd
  | g -> t1
  -- it's a tie and it's even
  | otherwise -> t0
  where
    i = n - 1
    g = testBit a n
    r = testBit a i
    t0 = shiftR a n
    t1 = t0 + 1

roundEvenOverflow :: forall a . (Bits a, Integral a) => Int -> a -> (a, Bool)
roundEvenOverflow n a = (a', overflow)
  where
    a' = roundEven n a
    overflow = (highestSetBit a - n) /= highestSetBit a'

highestSetBit :: (Integral b, Integral a) => a -> b
highestSetBit n = floor $ logBase (2 :: Double) $ fromIntegral n

-- ** Instances for native floats

-- | Read value of type @from@ as type @to@ via pointer. Used to cast
-- any C type to a binary type (Word).
viaStorable :: forall from to . (Storable from, Storable to) => from -> IO to
viaStorable f = do
  ptr :: Ptr from <- malloc @from
  poke ptr f *> peek (castPtr ptr) <* free ptr

instance Bits Float where
  testBit f ix = testBit (unsafePerformIO $ viaStorable @_ @Word32 f) ix
instance Bits Double where
  testBit f ix = testBit (unsafePerformIO $ viaStorable @_ @Word64 f) ix

-- instance Enum Float where
-- instance Enum Double where

-- | Positive infinity
n_inf :: Float
n_inf = 1/0

-- | Non-signaling NaN
n_nan :: Float
n_nan = 0/0

-- * Finite binary

class FiniteBinary a where
  type Width a :: Natural

instance FiniteBinary Word8  where type Width Word8  = 8
instance FiniteBinary Word16 where type Width Word16 = 16
instance FiniteBinary Word32 where type Width Word32 = 32
instance FiniteBinary Word64 where type Width Word64 = 64

instance FiniteBinary Float  where type Width Float  = 32
instance FiniteBinary Double where type Width Double = 64

-- instance (Bits a, FiniteBinary a, KnownNat (Width a)) => FiniteBits a where
--   finiteBitSize _ = fromIntegral (natVal @(Width a) Proxy)
