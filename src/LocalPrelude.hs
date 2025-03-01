module LocalPrelude
  ( module LocalPrelude
  , module Export
  ) where

import Prelude as Export hiding (exponent, significand)
import Data.Proxy
import GHC.TypeLits
import Debug.Trace as Export
import Numeric.Natural as Export
import Data.List as Export
import Data.Ratio as Export
import Data.Maybe as Export
import Data.Function as Export ((&))

-- * Helpers

u :: a
u = undefined

-- | Proxy-less/AllowAmbiguousTypes way to get value level integer from KnownNat
integerVal :: forall e . KnownNat e => Integer
integerVal = natVal @e Proxy

intVal :: forall n a . (KnownNat n, Num a) => a
intVal = fromIntegral (integerVal @n)
