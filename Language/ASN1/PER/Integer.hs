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
   , from2sComplement
   ) where

import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Control.Monad.State

g :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h' :: Integer -> Integer -> BitPut
h' p 0 =
   do putNBits (fromIntegral p) (0::Word8)
h' 0 n =
   do putNBits 1 (n `mod` 2)
      h' 7 (n `div` 2)
h' p n =
   do putNBits 1 (n `mod` 2)
      h' (p-1) (n `div` 2)

h'' 0 =
   do p <- get
      lift $ putNBits (fromIntegral (p+1)) (0::Word8)
      
h'' n =
   do p <- get
      case p of
         0 -> 
            do put 7
               h'' (n `div` 2)
               lift $ putNBits 1 (n `mod` 2)
         otherwise -> 
            do put (p-1)
               h'' (n `div` 2)
               lift $ putNBits 1 (n `mod` 2)

l n = genericLength ((flip (curry (unfoldr g)) 7) (-n-1)) + 1

to2sComplement3 :: Integer -> BitPut
to2sComplement3 n
   | n >= 0 = do h' 7 n
                 putNBits 1 (0::Word8)
   | otherwise = h' 8 (2^p + n)
   where
      p = l n

to2sComplement4 :: Integer -> BitPut
to2sComplement4 = undefined

to2sComplement :: Integer -> BL.ByteString
to2sComplement n =
   BL.reverse (BL.map reverseBits (runBitPut (to2sComplement3 n)))

bottomNBits :: Int -> Word8
bottomNBits 0 = 0
bottomNBits 1 = 0x01
bottomNBits 2 = 0x03
bottomNBits 3 = 0x07
bottomNBits 4 = 0x0f
bottomNBits 5 = 0x1f
bottomNBits 6 = 0x3f
bottomNBits 7 = 0x7f
bottomNBits 8 = 0xff
bottomNBits x = error ("bottomNBits undefined for " ++ show x)

rightShift :: Int -> BL.ByteString -> BL.ByteString
rightShift 0 = id
rightShift n = snd . BL.mapAccumL f 0 where
  f acc b = (b .&. (bottomNBits n), (b `shiftR` n) .|. (acc `shiftL` (8 - n)))

fromNonNegativeBinaryInteger :: Integer -> BL.ByteString -> Integer
fromNonNegativeBinaryInteger r x =
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` (fromIntegral bSize)
      bSize = bitSize (head ys)
      ys = reverse (BL.unpack (rightShift (fromIntegral s) x))
      zs = map ((2^bSize)^) [0..genericLength ys]

from2sComplement :: Num a => BL.ByteString -> a
from2sComplement a = x
   where
      l = fromIntegral (BL.length a)
      b = l*8 - 1
      (z:zs) = BL.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

toNonNegativeBinaryInteger :: Integer -> Integer -> BitPut
toNonNegativeBinaryInteger _ 0 = return ()
toNonNegativeBinaryInteger 0 w = toNonNegativeBinaryInteger 0 (w `div` 2) >> putNBits 1 (0::Word8)
toNonNegativeBinaryInteger n w = toNonNegativeBinaryInteger (n `div` 2) (w `div` 2) >> putNBits 1 (n `mod` 2)

reverseBits :: Word8 -> Word8
reverseBits = reverseBits3 . reverseBits2 . reverseBits1

reverseBits1 :: Word8 -> Word8
reverseBits1 x = shiftR x 4 .|. shiftL x 4

reverseBits2 :: Word8 -> Word8
reverseBits2 x = shiftR (x .&. 0xcc) 2 .|. shiftL (x .&. 0x33) 2

reverseBits3 :: Word8 -> Word8
reverseBits3 x = shiftR (x .&. 0xaa) 1 .|. shiftL (x .&. 0x55) 1
