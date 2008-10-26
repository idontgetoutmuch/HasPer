module Main where

import Language.ASN1.PER.IntegerAux
import Tests.Integer
import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Test.LazySmallCheck

{-
type BitStream = [Int]

h b = map fromIntegral . reverse . flip (curry (unfoldr g)) b

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
-}

instance Serial Word8 where
   series d = drawnFrom (map fromIntegral [0..d])

-- prop_RevRev :: Word8 -> Bool
prop_RevRev x =
   reverseBits (reverseBits x) == x

-- prop_From2sTo2s :: Integer -> Bool
prop_From2sTo2s x =
   from2sComplement (to2sComplement x) == x

-- prop_FromNonNegToNonNeg :: (Integer,Integer) -> Bool
prop_FromNonNegToNonNeg (n,w) =
   n >= 0 && w >= n ==> fromNonNegativeBinaryInteger (fromIntegral (bitWidth w)) (runBitPut (toNonNegativeBinaryInteger n w)) == n

{-
bitWidth n = genericLength (toNonNegativeBinaryInteger' (n,n))

bitPutify :: BitStream -> BitPut
bitPutify = mapM_ (putNBits 1)
-}

prop_NNBIntBits :: (Integer,Integer) -> Bool
prop_NNBIntBits (n,w) =
   n >=0 && w >= n ==> runBitPut (bitPutify (toNonNegativeBinaryInteger' (n,w))) == runBitPut (toNonNegativeBinaryInteger n w)

prop_2sComplement :: Integer -> Bool
prop_2sComplement n =
   runBitPut (bitPutify (to2sComplement' n)) == to2sComplement n

prop_2sComplement' :: Integer -> Bool
prop_2sComplement' n =
   runBitPut (to2sComplement'' n) == to2sComplement n

main = 
   do putStrLn "Checking reverse of reverse..."
      smallCheck 15 prop_RevRev
      putStrLn "Checking bitPut 2s complement using reverse == bitPut 2s complement..."
      smallCheck 15 prop_2sComplement'
      putStrLn "Checking unfolded 2s complement = bitPut 2s complement..."
      smallCheck 15 prop_2sComplement
      putStrLn "Checking from 2s complement of to 2s complement..."
      smallCheck 15 prop_From2sTo2s
      putStrLn "Checking unfolded non-negative binary integer = bitPut non-negative binary integer..."
      smallCheck 15 prop_NNBIntBits
      putStrLn "Checking from non-negative binary integer of to non-negative binary integer..."
      smallCheck 15 prop_FromNonNegToNonNeg
