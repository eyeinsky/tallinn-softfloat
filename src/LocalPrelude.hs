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
import Text.Read

-- * Helpers

u :: a
u = undefined

-- | Proxy-less/AllowAmbiguousTypes way to get value level integer from KnownNat
integerVal :: forall e . KnownNat e => Integer
integerVal = natVal @e Proxy

intVal :: forall n a . (KnownNat n, Num a) => a
intVal = fromIntegral (integerVal @n)

traceLabelShow :: Show a => String -> a -> a
traceLabelShow label a = trace (label <> " < " <> show a <> " >") a

readLabel :: Read a => String -> String -> a
readLabel label str = case readEither str of
  Right v -> v
  Left msg -> error $ label <> ": value: " <> str <> ", error: " <> msg
