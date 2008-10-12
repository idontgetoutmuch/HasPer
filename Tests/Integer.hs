module Main where

import Language.ASN1.PER.Integer
import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Test.LazySmallCheck

type BitStream = [Int]

to2sComplement' :: Integer -> BitStream
to2sComplement' n
   | n >= 0 = 0:(h 7 n)
   | otherwise = h 8 (2^p + n)
   where
      p = length (h 7 (-n-1)) + 1

g :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h b = map fromIntegral . reverse . flip (curry (unfoldr g)) b

l n = genericLength ((flip (curry (unfoldr g)) 7) (-n-1)) + 1

toNonNegativeBinaryIntegerAux (_,0) = Nothing
toNonNegativeBinaryIntegerAux (0,w) = Just (0, (0, w `div` 2))
toNonNegativeBinaryIntegerAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

toNonNegativeBinaryInteger' :: (Integer, Integer) -> BitStream
toNonNegativeBinaryInteger'
    = reverse . (map fromInteger) . unfoldr toNonNegativeBinaryIntegerAux

reverseBits :: Word8 -> Word8
reverseBits = reverseBits3 . reverseBits2 . reverseBits1

reverseBits1 :: Word8 -> Word8
reverseBits1 x = shiftR x 4 .|. shiftL x 4

reverseBits2 :: Word8 -> Word8
reverseBits2 x = shiftR (x .&. 0xcc) 2 .|. shiftL (x .&. 0x33) 2

reverseBits3 :: Word8 -> Word8
reverseBits3 x = shiftR (x .&. 0xaa) 1 .|. shiftL (x .&. 0x55) 1

instance Serial Word8 where
   series d = drawnFrom (map fromIntegral [0..d])

prop_RevRev :: Word8 -> Bool
prop_RevRev x =
   reverseBits (reverseBits x) == x

prop_From2sTo2s :: Integer -> Bool
prop_From2sTo2s x =
   from2sComplement (to2sComplement x) == x

prop_FromNonNegToNonNeg :: (Integer,Integer) -> Bool
prop_FromNonNegToNonNeg (n,w) =
   n >= 0 && w >= n ==> fromNonNegativeBinaryInteger (fromIntegral (bitWidth w)) (runBitPut (toNonNegativeBinaryInteger n w)) == n

bitWidth n = genericLength (toNonNegativeBinaryInteger' (n,n))

bitPutify :: BitStream -> BitPut
bitPutify = mapM_ (putNBits 1)

prop_NNBIntBits :: (Integer,Integer) -> Bool
prop_NNBIntBits (n,w) =
   n >=0 && w >= n ==> runBitPut (bitPutify (toNonNegativeBinaryInteger' (n,w))) == runBitPut (toNonNegativeBinaryInteger n w)

prop_2sComplement :: Integer -> Bool
prop_2sComplement n =
   runBitPut (bitPutify (to2sComplement' n)) == to2sComplement n

main = 
   do putStrLn "Checking reverse of reverse..."
      smallCheck 15 prop_RevRev
      putStrLn "Checking unfolded 2s complement = bitPut 2s complement..."
      smallCheck 15 prop_2sComplement
      putStrLn "Checking from 2s complement of to 2s complement..."
      smallCheck 15 prop_From2sTo2s
      putStrLn "Checking unfolded non-negative binary integer = bitPut non-negative binary integer..."
      smallCheck 15 prop_NNBIntBits
      putStrLn "Checking from non-negative binary integer of to non-negative binary integer..."
      smallCheck 15 prop_FromNonNegToNonNeg
