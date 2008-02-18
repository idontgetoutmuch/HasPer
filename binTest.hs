module Main where

import qualified Data.ByteString as B
import Data.Word
import Data.Bits
import IO
import Data.List

import qualified Data.Binary.Strict.BitGet as BG

import qualified Data.ByteString.Char8 as BC
import Data.ByteString.Internal (w2c)
import qualified Data.ByteString.Lazy.Char8 as BLC

import Text.Printf (printf)


t :: (Eq a, Show a) => [Word8] -> BG.BitGet a -> a -> Bool
t bytes m v = if result == v then True else error (show (bytes, v, result)) where
  Right result = BG.runBitGet (B.pack bytes) m

foos 0 = return []
foos n =
   do x <- BG.getBit
      xs <- foos (n-1)
      return ((case x of False -> 0; True -> 1):xs)

foos8 0 = return []
foos8 n =
   do x <- BG.getWord8
      xs <- foos8 (n-1)
      return (x:xs)

test =
   do h <- openFile "foobarbaz" ReadMode
      b <- B.hGetContents h
      let ebms = test2 b 
      case ebms of
         Left s    -> return s
         Right bms -> return (concat ((map (show . B.unpack) bms)))

test1 =
   do bm1 <- BG.getRightByteString 2
      bm2 <- BG.getRightByteString 2
      return [bm1,bm2]
      
test2 bs = BG.runBitGet bs test1
      
data S = S {-# UNPACK #-} !B.ByteString  -- ^ output
           {-# UNPACK #-} !Word8  -- ^ bit offset in current byte
           {-# UNPACK #-} !Word8  -- ^ current byte

newtype PutBit a = PutBit { unPut :: S -> (a,S) }

instance Functor PutBit where
   fmap f m = PutBit (\s -> let (a,s') = unPut m s in (f a,s'))

instance Monad PutBit where
   return a = PutBit (\s -> (a,s))
   m >>= k = PutBit (\s -> let (a,s')  = unPut m s in unPut (k a) s')

get :: PutBit S
get = PutBit (\s -> (s,s))

put :: S -> PutBit ()
put s = PutBit (const ((), s))

writeN :: Word8 -> PutBit ()
writeN n =
   do S bytes boff curr <- get
      let bit = n .&. 0x01
          newCurr = curr .|. (shiftL bit (fromIntegral boff))
          newBoff = boff + 1
      if newBoff == 9
         then put (S (B.cons curr bytes) 1 bit)
         else put (S bytes newBoff newCurr)

foo = do writeN 1
         writeN 0
         writeN 1
         writeN 0
         writeN 1
         writeN 0
         writeN 1
         writeN 0
         writeN 1
         writeN 0
         writeN 1
         writeN 0
         writeN 1

bar [] = return ()
bar (x:xs) = do writeN x
                bar xs

runBitPut m =
   let (_,s) = unPut m (S B.empty 0 0) 
       (S bytes boff curr) = s
       allBits = B.cons curr bytes
   in 
      (leftShift (fromIntegral (8-boff)) allBits,hexDumpString allBits,hexDumpString (leftShift (fromIntegral (8-boff)) allBits),boff,curr)

leftShift :: Int -> B.ByteString -> B.ByteString
leftShift 0 = id
leftShift n = snd . B.mapAccumR f 0 where
  f acc b = (b `shiftR` (8 - n), (b `shiftL` n) .|. acc)

ennb :: (Integer,Integer) -> PutBit ()
ennb = mUnfoldr h

h (_,0) = Nothing
h (0,w) = Just (0, (0, w `div` 2))
h (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

mUnfoldr f b =
   case f b of
      Just (a,new_b) -> do writeN a
                           mUnfoldr f new_b
      Nothing -> return ()

type BitStream = [Word8]

encodeNNBIntOctets :: Integer -> BitStream
encodeNNBIntOctets =
   reverse . (map fromInteger) . flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))

      
encodeNNBIntBits :: (Integer, Integer) -> BitStream
encodeNNBIntBits
    = reverse . (map fromInteger) . unfoldr h
      where
        h (_,0) = Nothing
        h (0,w) = Just (0, (0, w `div` 2))
        h (n,w) = Just (n `mod` 2, (n `div` 2, w `div` 2))

hexDumpString :: B.ByteString -> BLC.ByteString
hexDumpString = BLC.fromChunks . dumpLine (0 :: Int) where
  dumpLine offset bs
    | B.null bs = []
    | otherwise = line : (dumpLine (offset + 16) $ B.drop 16 bs) where
        line = s $ a ++ b ++ "  " ++ c ++ padding ++ right ++ newline
        s = BC.pack
        a = printf "%08x  " offset
        b = concat $ intersperse " " $ map (printf "%02x") $ B.unpack $ B.take 8 bs
        c = concat $ intersperse " " $ map (printf "%02x") $ B.unpack $ B.take 8 $ B.drop 8 bs
        padding = replicate paddingSize ' '
        paddingSize = 2 + (16 - (min 16 $ B.length bs)) * 3 - if B.length bs <= 8 then 1 else 0
        right = map safeChar $ B.unpack $ B.take 16 bs
        newline = "\n"
        safeChar c
          | c >= 32 && c <= 126 = w2c c
          | otherwise = '.'