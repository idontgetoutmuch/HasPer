module Language.ASN1.PER.Integer (
   encodeNNBIntBits
   ) where

import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString.Lazy as BL
import Data.Binary.BitPut
import Test.LazySmallCheck

type BitStream = [Int]

{-
to2sComplement :: Integer -> BitStream
to2sComplement n
   | n >= 0 = 0:(h 7 n)
   | otherwise = h 8 (2^p + n)
   where
      p = length (h 7 (-n-1)) + 1
-}

g :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h b = map fromIntegral . reverse . flip (curry (unfoldr g)) b

h' :: Integer -> Integer -> BitPut
h' p 0 =
   do putNBits (fromIntegral p) (0::Word8)
h' 0 n =
   do putNBits 1 (n `mod` 2)
      h' 7 (n `div` 2)
h' p n =
   do putNBits 1 (n `mod` 2)
      h' (p-1) (n `div` 2)

l n = genericLength ((flip (curry (unfoldr g)) 7) (-n-1)) + 1

to2sComplement' :: Integer -> BitPut
to2sComplement' n
   | n >= 0 = do h' 7 n
                 putNBits 1 (0::Word8)
   | otherwise = h' 8 (2^p + n)
   where
      p = l n

to2sComplement'' :: Integer -> BL.ByteString
to2sComplement'' n =
   BL.reverse (BL.map reverseBits (runBitPut (to2sComplement' n)))

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

fromNonNeg r x =
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` bSize
      bSize = bitSize (head ys)
      ys = reverse (BL.unpack (rightShift s x))
      zs = map ((2^bSize)^) [0..genericLength ys]

from2sComplement a = x
   where
      l = fromIntegral (BL.length a)
      b = l*8 - 1
      (z:zs) = BL.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

encodeNNBIntBitsAux (_,0) = Nothing
encodeNNBIntBitsAux (0,w) = Just (0, (0, w `div` 2))
encodeNNBIntBitsAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

encodeNNBIntBits' :: (Integer, Integer) -> BitStream
encodeNNBIntBits'
    = reverse . (map fromInteger) . unfoldr encodeNNBIntBitsAux

encodeNNBIntBits :: Integer -> Integer -> BitPut
encodeNNBIntBits _ 0 = return ()
encodeNNBIntBits 0 w = encodeNNBIntBits 0 (w `div` 2) >> putNBits 1 (0::Word8)
encodeNNBIntBits n w = encodeNNBIntBits (n `div` 2) (w `div` 2) >> putNBits 1 (n `mod` 2)

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
   from2sComplement (to2sComplement'' x) == x

prop_FromNonNegToNonNeg :: (Integer,Integer) -> Bool
prop_FromNonNegToNonNeg (n,w) =
   n >= 0 && w >= n ==> fromNonNeg (fromIntegral (bitWidth w)) (runBitPut (encodeNNBIntBits n w)) == n

bitWidth n = genericLength (encodeNNBIntBits' (n,n))

bitPutify :: BitStream -> BitPut
bitPutify = mapM_ (putNBits 1)

prop_NNBIntBits :: (Integer,Integer) -> Bool
prop_NNBIntBits (n,w) =
   n >=0 && w >= n ==> runBitPut (bitPutify (encodeNNBIntBits' (n,w))) == runBitPut (encodeNNBIntBits n w)

main = 
   do putStrLn "Checking reverse of reverse..."
      smallCheck 15 prop_RevRev
      putStrLn "Checking from 2s complement of to 2s complement..."
      smallCheck 15 prop_From2sTo2s
      putStrLn "Checking unfolded non-negative binary integer = monadic non-negative binary integer..."
      smallCheck 15 prop_NNBIntBits
      putStrLn "Checking from non-negative binary integer of to non-negative binary integer..."
      smallCheck 15 prop_FromNonNegToNonNeg
