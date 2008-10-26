{-# 
OPTIONS_GHC -fwarn-unused-imports
#-}

module Tests.Integer where

import Language.ASN1.PER.IntegerAux
import Data.List
import Data.Binary.BitPut

type BitStream = [Int]

h b = map fromIntegral . reverse . flip (curry (unfoldr nnbIterator)) b

to2sComplement' :: Integer -> BitStream
to2sComplement' n
   | n >= 0 = 0:(h 7 n)
   | otherwise = h 8 (2^p + n)
   where
      p = length (h 7 (-n-1)) + 1

toNonNegativeBinaryIntegerAux (_,0) = Nothing
toNonNegativeBinaryIntegerAux (0,w) = Just (0, (0, w `div` 2))
toNonNegativeBinaryIntegerAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

toNonNegativeBinaryInteger' :: (Integer, Integer) -> BitStream
toNonNegativeBinaryInteger'
    = reverse . (map fromInteger) . unfoldr toNonNegativeBinaryIntegerAux

bitWidth n = genericLength (toNonNegativeBinaryInteger' (n,n))

bitPutify :: BitStream -> BitPut
bitPutify = mapM_ (putNBits 1)
