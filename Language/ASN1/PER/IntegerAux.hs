-----------------------------------------------------------------------------
-- |
-- Module      : Language.ASN1.PER.IntegerAux
-- Copyright   : Dominic Steinitz
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Dominic Steinitz <dominic.steinitz@blueyonder.co.uk>
-- Stability   : experimental
--
-- TBD
-----------------------------------------------------------------------------
{-# 
OPTIONS_GHC -fwarn-unused-imports
#-}

module Language.ASN1.PER.IntegerAux
   ( toNonNegativeBinaryInteger
   , fromNonNegativeBinaryInteger
   , fromNonNegativeBinaryInteger'
   , to2sComplementUsingReverse
   , to2sComplement
   , from2sComplement
   , from2sComplement'
   , nnbIterator
   , reverseBits
   ) where

import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Control.Monad.State

nnbIterator :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
nnbIterator (0,0) = Nothing
nnbIterator (0,p) = Just (0,(0,p-1))
nnbIterator (n,0) = Just (n `rem` 2,(n `quot` 2,7))
nnbIterator (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h' :: Integer -> Integer -> BitPut
h' p 0 =
   do putNBits (fromIntegral p) (0::Word8)
h' 0 n =
   do putNBits 1 (n `mod` 2)
      h' 7 (n `div` 2)
h' p n =
   do putNBits 1 (n `mod` 2)
      h' (p-1) (n `div` 2)
  
to2sComplementReverse :: Integer -> BitPut
to2sComplementReverse n
   | n >= 0 = do h' 7 n
                 putNBits 1 (0::Word8)
   | otherwise = h' 8 (2^(l n) + n)

l n = genericLength ((flip (curry (unfoldr nnbIterator)) 7) (-n-1)) + 1

to2sComplementUsingReverse :: Integer -> BL.ByteString
to2sComplementUsingReverse n =
   BL.reverse (BL.map reverseBits (runBitPut (to2sComplementReverse n)))

-- h'' :: Integer -> StateT Word8 BitPut' ()
h'' 0 =
   do p <- get
      lift $ putNBits (fromIntegral p) (0::Word8)
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

to2sComplement :: Integer -> BitPut
to2sComplement n
   | n >= 0    = putNBits 1 (0::Word8) >> runStateT (h'' n) 7             >> return ()
   | otherwise =                          runStateT (h'' (2^(l n) + n)) 8 >> return ()

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

from2sComplement' :: Num a => B.ByteString -> a
from2sComplement' a = x
   where
      l = fromIntegral (B.length a)
      b = l*8 - 1
      (z:zs) = B.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

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

rightShift' :: Int -> B.ByteString -> B.ByteString
rightShift' 0 = id
rightShift' n = snd . B.mapAccumL f 0 where
  f acc b = (b .&. (bottomNBits n), (b `shiftR` n) .|. (acc `shiftL` (8 - n)))

fromNonNegativeBinaryInteger :: Integer -> BL.ByteString -> Integer
fromNonNegativeBinaryInteger r x =
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` (fromIntegral bSize)
      bSize = bitSize (head ys)
      ys = reverse (BL.unpack (rightShift (fromIntegral s) x))
      zs = map ((2^bSize)^) [0..genericLength ys]

fromNonNegativeBinaryInteger' :: Integer -> B.ByteString -> Integer
fromNonNegativeBinaryInteger' r x =
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` (fromIntegral bSize)
      bSize = bitSize (head ys)
      ys = reverse (B.unpack (rightShift' (fromIntegral s) x))
      zs = map ((2^bSize)^) [0..genericLength ys]


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
