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
   , fromNonNegativeBinaryInteger'
   , to2sComplement
   , from2sComplement
   , from2sComplement'
   ) where

import qualified Language.ASN1.PER.IntegerAux as I
import Data.Binary.BitPut
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString as B

{-|
'toNonNegativeBinaryInteger' takes two 'Integer' arguments and encodes
the first in the minimum number of bits required to encode the second.
For example, 'toNonNegativeBinaryInteger' 3 11 will encode 3 in the number
of bits required to encode 11: 0011. Note, the result is not defined if
either of the arguments are negative or if the second argument is smaller
than the first.
-}
toNonNegativeBinaryInteger :: Integer -> Integer -> BitPut
toNonNegativeBinaryInteger = I.toNonNegativeBinaryInteger

{-|
'fromNonNegativeBinaryInteger' takes an 'Integer' number of bits and and
'ByteString' and decodes that number of bits as binary into an 'Integer'. 
For example, 'fromNonNegativeBinaryInteger' 4 will take the first 4 bits of
a 'ByteString' and decode it into an 'Integer'.
-}
fromNonNegativeBinaryInteger :: Integer -> ByteString -> Integer
fromNonNegativeBinaryInteger = I.fromNonNegativeBinaryInteger

{-|
'to2sComplement' takes an 'Integer' argument and encodes it
as two's complement (<http://en.wikipedia.org/wiki/2s_complement>)
in the smallest number of bytes.
-}
to2sComplement :: Integer -> BitPut
to2sComplement = I.to2sComplement

{-|
'from2sComplement' takes a 'ByteString' argument and decodes the
bits as two's complement (<http://en.wikipedia.org/wiki/2s_complement>)
into a "number" 'Num' a.
-}
from2sComplement :: Num a => ByteString -> a
from2sComplement = I.from2sComplement

fromNonNegativeBinaryInteger' = I.fromNonNegativeBinaryInteger'

from2sComplement' :: Num a => B.ByteString -> a
from2sComplement' = I.from2sComplement'