-----------------------------------------------------------------------------
-- |
-- Module      : Language.ASN1.PER.Integer
-- Copyright   : Dominic Steinitz
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Dominic Steinitz <dominic.steinitz@blueyonder.co.uk>
-- Stability   : experimental
--
-- TBD
-----------------------------------------------------------------------------
module Language.ASN1.PER.Integer
   ( toNonNegativeBinaryInteger
   , fromNonNegativeBinaryInteger
   , to2sComplement
   , from2sComplement,
   ) where

import qualified Language.ASN1.PER.IntegerAux as I
import Data.Binary.BitPut
import Data.ByteString.Lazy (ByteString)

toNonNegativeBinaryInteger :: Integer -> Integer -> BitPut
toNonNegativeBinaryInteger = I.toNonNegativeBinaryInteger

fromNonNegativeBinaryInteger :: Integer -> ByteString -> Integer
fromNonNegativeBinaryInteger = I.fromNonNegativeBinaryInteger

to2sComplement :: Integer -> BitPut
to2sComplement = I.to2sComplement

from2sComplement :: ByteString -> Integer
from2sComplement = I.from2sComplement