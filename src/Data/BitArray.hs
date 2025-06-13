{-# LANGUAGE TypeFamilies #-}
module Data.BitArray
  ( module Data.BitArray
  , module Data.Bit
  ) where

import LocalPrelude
import Data.Bits
import GHC.TypeLits
import Data.Char (intToDigit)
import Numeric (showIntAtBase)

import Data.Bit

type T = Natural
data BitArray (w :: Natural) where
  BitArray :: KnownNat w => { bitArrayInt :: T } -> BitArray w

-- | TODO think about the design of this
upcast :: forall a b . (KnownNat a, KnownNat b, a <= b) => BitArray a -> BitArray b
upcast (BitArray a) = BitArray @b a

mkOp2 :: KnownNat c => (T -> T -> T) -> BitArray a -> BitArray b -> BitArray c
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

instance FiniteBinary (BitArray w) where
  type Width (BitArray w) = w
instance KnownNat w => FiniteBits (BitArray w) where
  finiteBitSize _ = intVal @w

instance Show (BitArray w) where
  show (BitArray a) = "0b" <> foldl (\acc i -> boolBitChar (testBit a i) : acc) [] [0 .. (intVal @w) - 1]

instance KnownNat w => Bounded (BitArray w) where
  minBound = BitArray 0
  maxBound = foldl' (\acc i -> setBit acc i) 0 [0 .. intVal @w - 1 ]

instance KnownNat w => Real (BitArray w) where
  toRational (BitArray a) = toRational a

instance KnownNat w => Enum (BitArray w) where
  toEnum = BitArray . toEnum
  fromEnum (BitArray n) = fromEnum n

instance KnownNat w => Integral (BitArray w) where
  -- quot :: a -> a -> a
  -- rem :: a -> a -> a
  -- div :: a -> a -> a
  -- mod :: a -> a -> a
  quotRem (BitArray a) (BitArray b) = let (a', b') = quotRem a b  --  :: a -> a -> (a, a)
    in (BitArray a', BitArray b')
  -- divMod :: a -> a -> (a, a)
  toInteger (BitArray n) = toInteger n -- :: a -> Integer
  -- {-# MINIMAL quotRem, toInteger #-}

showIntBits :: T -> String
showIntBits a = if a < 0
  then '1' : showPosIntBits (abs a)
  else '0' : showPosIntBits a

showPosIntBits :: T -> String
showPosIntBits a = showIntAtBase 2 intToDigit a ""

-- * Bit list interop

-- | From little-endian bit list to BitArray
bitsToArrayLE :: forall w . KnownNat w => [Bit] -> BitArray w
bitsToArrayLE = foldl' setBit (BitArray 0) . map fst . filter ((I ==) . snd) . zip [0 .. intVal @w - 1]

-- | From big-endian bit list to BitArray
bitsToArrayBE :: forall w . KnownNat w => [Bit] -> BitArray w
bitsToArrayBE bits = bits
  & zip [l, l - 1 .. 0]        -- zip indices
  & filter ((I ==) . snd)      -- keep only 1 bits
  & map fst                    -- take indices
  & foldl' setBit (BitArray 0) -- set 1 indices to 1
  where
    l = intVal @w - 1
