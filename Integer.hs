import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString as B
import Data.Binary.Strict.BitUtil (rightShift)
import Data.Binary.Strict.BitPut
import Test.LazySmallCheck

type BitStream = [Int]

to2sComplement :: Integer -> BitStream
to2sComplement n
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

h' :: Integer -> Integer -> BitPut
h' p 0 =
   do putNBits (fromIntegral p) (0::Word8)
h' 0 n =
   do putNBits 1 (n `rem` 2)
      h' 7 (n `quot` 2)
h' p n =
   do putNBits 1 (n `rem` 2)
      h' (p-1) (n `quot` 2)

l n = genericLength ((flip (curry (unfoldr g)) 7) (-n-1)) + 1

to2sComplement' :: Integer -> BitPut
to2sComplement' n
   | n >= 0 = do h' 7 n
                 putNBits 1 (0::Word8)
   | otherwise = h' 8 (2^p + n)
   where
      p = l n

to2sComplement'' :: Integer -> B.ByteString
to2sComplement'' n =
   B.map reverseBits (runBitPut (to2sComplement' n))

fromNonNeg r x =
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` bSize
      bSize = bitSize (head ys)
      ys = reverse (B.unpack (rightShift s x))
      zs = map ((2^bSize)^) [0..genericLength ys]

from2sComplement a = x
   where
      l = fromIntegral (B.length a)
      b = l*8 - 1
      (z:zs) = B.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

encodeNNBIntBitsAux (_,0) = Nothing
encodeNNBIntBitsAux (0,w) = Just (0, (0, w `div` 2))
encodeNNBIntBitsAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

encodeNNBIntBits :: (Integer, Integer) -> BitStream
encodeNNBIntBits
    = reverse . (map fromInteger) . unfoldr encodeNNBIntBitsAux

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

main = smallCheck 255 prop_RevRev