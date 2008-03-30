-----------------------------------------------------------------------------
-- |
-- Module      :  Language.ASN1.TLV
-- Copyright   :  (c) Dominic Steinitz 2005 - 2008
-- License     :  BSD3
-- 
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  portable
--
-- Decode binary BER into abstract an abstract representation of tag,
-- length and value ensuring that the lengths are consistent.
--
-----------------------------------------------------------------------------

module TLV (
   tlv
	      ) where
import Data.Bits
import Control.Exception
import Control.Monad.State
import Control.Monad.Error
import System.IO.Error
import Language.ASN1.BER (Encoding(..),Length)
import Language.ASN1.Utils (msb,fromOctets)
import Language.ASN1 (TagType(..))
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.Strict.BitUtil as BU

-- The bit decoder will (by design) never lie about lengths
-- because it can check these. It may lie (if that's what it's being
-- told) about numbers of components because it can't check these 
-- without having the ASN.1 definitions.

getOctets l = 
   if l <= 0 
      then return []
      else do x  <- BG.getWord8
              xs <- getOctets (l-1)
              return (x:xs)

getLength =
   do x <- BG.getWord8
      let isShort   = not (testBit x msb)
          shortform = fromIntegral x
          length    = fromIntegral (clearBit x msb) in 
         if x == 0x80
            then fail "Indefinite length not supported"
            else if isShort
               then return (1,shortform)
               else do xs <- getOctets length
                       let longform = fromOctets 256 xs in
                          return (length+1,longform)

tagValueLen = 5
tagConstructionLen = 1
tagTypeLen = 2

tlv :: BG.BitGet (Length,Encoding)
tlv = tlv_

tlv_ :: BG.BitGet (Length,Encoding)
tlv_ =  
   do tagValueVal        <- BG.getLeftByteString tagValueLen
      tagConstructionVal <- BG.getLeftByteString tagConstructionLen
      tagTypeVal         <- BG.getLeftByteString tagTypeLen
      let tagType  = toEnum . fromIntegral . head . B.unpack . (BU.rightShift (8 - tagTypeLen)) $ tagTypeVal
          tagValue = fromIntegral . head . B.unpack . (BU.rightShift (8 - tagValueLen)) $ tagValueVal
          tagConstruction = fromIntegral . head . B.unpack . (BU.rightShift (8 - tagConstructionLen)) $ tagConstructionVal
      if tagValue /= 31
         then do (ll,l) <- getLength
                 f 1 tagConstruction tagType tagValue ll l
         else do xs <- getTagOctets
                 let longform = fromIntegral (fromOctets 128 xs)
                 (ll,l) <- getLength
                 f (fromIntegral $ length xs) tagConstruction tagType longform ll l
   where f tl tcv tt tv ll l = 
            if tcv == 0
               then do xs <- getOctets l
                       let x = Primitive tt tv l xs
                       return (tl+ll+l,x)
               else do ys <- tlvs_ l
                       let x = Constructed tt tv l ys
                       return (tl+ll+l,x)

getTagOctets = 
   do x <- BG.getWord8
      if not (testBit x msb)
         then return [x]
         else do xs <- getTagOctets
                 return ((clearBit x msb):xs)

tlvs_ curLen
   | curLen < 0  = fail "Codec.ASN1.TLV.tlvs_: trying to decode a negative number of octets"
   | curLen == 0 = return []
   | otherwise   = do (l,x)  <- tlv_ 
                      ys     <- tlvs_ (curLen-l)
                      return (x:ys)
