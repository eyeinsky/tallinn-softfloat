module Data.BitArray where

import LocalPrelude
import Data.Bits
import GHC.TypeLits
import Data.Char (intToDigit)
import Numeric (showIntAtBase)


type T = Natural
data BitArray (w :: Natural) where
  BitArray :: KnownNat w => { bitArrayInt :: T } -> BitArray w

mkOp2 :: (T -> T -> T) -> BitArray a -> BitArray a -> BitArray a
mkOp2 op (BitArray a) (BitArray b) = BitArray $ op a b

mkOp1 :: (T -> T) -> BitArray a -> BitArray a
mkOp1 op (BitArray a) = BitArray $ op a

instance KnownNat w => Bits (BitArray w) where
  (.&.) = mkOp2 (.&.)
  (.|.) = mkOp2 (.|.)
  xor = mkOp2 xor
  complement (BitArray i) = BitArray $ foldl' (\i' ix -> if testBit i' ix then clearBit i' ix else setBit i' ix) i [0 .. (intVal @w) - 1]

  shift (BitArray n) i = BitArray $ zeroOverflow $ shift n i
    where
      zeroOverflow nat = foldl' (clearBit) nat [(intVal @w) .. (intVal @w) + i]

  rotate (BitArray i) n = BitArray (rotate i n)
  bitSize = finiteBitSize
  bitSizeMaybe = Just . finiteBitSize
  isSigned = isSigned . bitArrayInt
  testBit (BitArray i) n = testBit i n
  bit ix = BitArray (bit ix)
  popCount = popCount . bitArrayInt

instance KnownNat w => Num (BitArray w) where
  (+) = mkOp2 (+)
  (-) = mkOp2 (-)
  (*) = mkOp2 (*)
  abs a = a
  signum _ = 1
  fromInteger = BitArray . fromInteger

instance Eq (BitArray w) where BitArray a == BitArray b = a == b
instance Ord (BitArray w) where compare (BitArray a) (BitArray b) = compare a b

instance KnownNat w => FiniteBits (BitArray w) where
  finiteBitSize _ = intVal @w

instance Show (BitArray w) where
  show (BitArray a) = "0b" <> foldl (\acc i -> boolBitChar (testBit a i) : acc) [] [0 .. (intVal @w) - 1]

instance KnownNat w => Bounded (BitArray w) where
  minBound = BitArray 0
  maxBound = foldl' (\acc i -> setBit acc i) 0 [0 .. intVal @w - 1 ]

boolBitChar :: Bool -> Char
boolBitChar = \case
  True -> '1'
  False -> '0'

showIntBits :: T -> String
showIntBits a = if a < 0
  then '1' : showPosIntBits (abs a)
  else '0' : showPosIntBits a

showPosIntBits :: T -> String
showPosIntBits a = showIntAtBase 2 intToDigit a ""

-- * Helpers

lastBitIndex :: FiniteBits a => a -> Int
lastBitIndex a = finiteBitSize a - 1

newIndexes :: FiniteBits a => (Int -> Int) -> a -> [Int]
newIndexes op a = map fst $ filter (\(j, b) -> j <= lastBitIndex' && b) $ map (\j -> (op j, testBit a j)) [0 .. lastBitIndex']
  where
    lastBitIndex' = lastBitIndex a

-- * Bit

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

-- | List of bits, infinite, little-endian.
bitListPrim :: Bits a => a -> [Bit]
bitListPrim a = map (getBit a) [0..]

-- | Calculate a bitlist for integrals by capping the list when
-- argument is reached. Big-endian, starts always with a @I@, possibly
-- infinite.
bitList :: forall a . (Bits a, Integral a) => a -> [Bit]
bitList a = go ([], 0) $ zip [0..] $ bitListPrim a
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

-- | From little-endian bits to BitArray
bitsToArrayLE :: forall w . KnownNat w => [Bit] -> BitArray w
bitsToArrayLE = foldl' setBit (BitArray 0) . map fst . filter ((I ==) . snd) . zip [0 .. intVal @w - 1]

-- | From big-endian bits to BitArray
bitsToArrayBE :: forall w . KnownNat w => [Bit] -> BitArray w
bitsToArrayBE bits = bits
  & zip [l, l - 1 .. 0]        -- zip indices
  & filter ((I ==) . snd)      -- keep only 1 bits
  & map fst                    -- take indices
  & foldl' setBit (BitArray 0) -- set 1 indices to 1
  where
    l = intVal @w - 1

-- ** Show

bitChar :: Bit -> Char
bitChar = \case O -> '0'; I -> '1'

bitStringFinite :: FiniteBits a => a -> String
bitStringFinite = map bitChar . bitListFinite

toBitBoolListN :: Bits a => a -> Int -> [Bool]
toBitBoolListN a max = map (\i -> testBit a i) [max, max - 1 .. 0]

prettyBitList :: FiniteBits a => a -> String
prettyBitList a = map (\b -> if b then '1' else '0') $ dropWhile not $ toBitBoolListN a (finiteBitSize a)

binaryLiteral :: FiniteBits a => a -> String
binaryLiteral a = "0b" <> prettyBitList a

-- | Top bits of @a@ as [Bool], reversed
topBits :: FiniteBits a => a -> Int -> [Bool]
topBits a n = foldl' (\acc i -> testBit a i : acc) [] $ take n [max, max - 1 .. 0]
  where
    max = finiteBitSize a - 1

-- * Bitlist

-- | Round bitlist to @n@ digits. The returned Bool indicates whether
-- by rounding up an additional 1 bit was added as the most
-- significant bit. Input/output are big-endian.
roundBits :: Int -> [Bit] -> ([Bit], Bool)
roundBits n bits = let
    (a, overflow) = splitAt n bits
    a' = reverse a -- little-endian
  in case overflow of
      -- first overflow bit is zero or there are no overflow bits => truncated
      [] -> (a, False)
      O : _ -> (a, False)
      I : rest -> if all (== O) rest
        then case a' of        -- it's a tie
          I : _ -> ceiling a'  -- remainder is odds => ceiling
          O : _ -> (a, False)  -- remainder is even => floor
          []    -> (a, False)  -- same
        else ceiling a'

  where
    ceiling a = let (x, y) = add1 a in (reverse x, y)

-- | Add 1 to little-endian bit list. Second member signifies whether
-- an extra digit was added.
add1 :: [Bit] -> ([Bit], Bool)
add1 bits' = case bits' of
  O : rest -> (I : rest, False)
  I : rest -> let (bs, o) = add1 rest in (O : bs, o)
  [] -> ([I], True)
