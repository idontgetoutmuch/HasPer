{-# 
OPTIONS_GHC -fwarn-unused-imports
#-}

module Tests.QuickCheck.Integer where

import Language.ASN1.PER.IntegerAux
import Tests.Integer
import Data.Word
import Data.Binary.BitPut
import Test.QuickCheck

instance Arbitrary Word8 where
   arbitrary =
      do n <- choose ((fromIntegral (minBound::Word8))::Int,
                      (fromIntegral (maxBound::Word8))::Int)
         return (fromIntegral n)

prop_RevRev x =
   reverseBits (reverseBits x) == x

prop_From2sTo2s x =
   from2sComplement (runBitPut (to2sComplement x)) == x

prop_FromNonNegToNonNeg (n,w) =
   n >= 0 && w >= n ==> fromNonNegativeBinaryInteger (fromIntegral (bitWidth w)) (runBitPut (toNonNegativeBinaryInteger n w)) == n


prop_NNBIntBits (n,w) =
   n >=0 && w >= n ==> runBitPut (bitPutify (toNonNegativeBinaryInteger' (n,w))) == runBitPut (toNonNegativeBinaryInteger n w)

prop_2sComplement n =
   runBitPut (bitPutify (to2sComplement' n)) == runBitPut (to2sComplement n)

prop_2sComplement' n =
   to2sComplementUsingReverse n == runBitPut (to2sComplement n)

tests = 
   do putStrLn "Checking reverse of reverse..."
      quickCheck prop_RevRev
      putStrLn "Checking bitPut 2s complement using reverse == bitPut 2s complement..."
      quickCheck prop_2sComplement'
      putStrLn "Checking unfolded 2s complement = bitPut 2s complement..."
      quickCheck prop_2sComplement
      putStrLn "Checking from 2s complement of to 2s complement..."
      quickCheck prop_From2sTo2s
      putStrLn "Checking unfolded non-negative binary integer = bitPut non-negative binary integer..."
      quickCheck prop_NNBIntBits
      putStrLn "Checking from non-negative binary integer of to non-negative binary integer..."
      quickCheck prop_FromNonNegToNonNeg
