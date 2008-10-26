{-# 
OPTIONS_GHC -fwarn-unused-imports
#-}

module Tests.SmallCheck.Integer where

import Language.ASN1.PER.IntegerAux
import Tests.Integer
import Data.Word
import Data.List
import Data.Binary.BitPut
import Test.LazySmallCheck

instance Serial Word8 where
   series d = drawnFrom (map fromIntegral [0..d])

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

testsAux n = 
   do putStrLn "Checking reverse of reverse..."
      smallCheck n prop_RevRev
      putStrLn "Checking bitPut 2s complement using reverse == bitPut 2s complement..."
      smallCheck n prop_2sComplement'
      putStrLn "Checking unfolded 2s complement = bitPut 2s complement..."
      smallCheck n prop_2sComplement
      putStrLn "Checking from 2s complement of to 2s complement..."
      smallCheck n prop_From2sTo2s
      putStrLn "Checking unfolded non-negative binary integer = bitPut non-negative binary integer..."
      smallCheck n prop_NNBIntBits
      putStrLn "Checking from non-negative binary integer of to non-negative binary integer..."
      smallCheck n prop_FromNonNegToNonNeg

tests = testsAux 257