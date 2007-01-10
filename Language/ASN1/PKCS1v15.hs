-----------------------------------------------------------------------------
-- |
-- Module      :  Codec.Encryption.RSA.PKCS1v15
-- Copyright   :  (c) Dominic Steinitz 2005
-- License     :  BSD-style (see the file ReadMe.tex)
--
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  portable
--
-- Functions and types to allow the encoding and decoding of the 
-- RSA PKCS1v1.5
-- signature scheme. See 
-- (<ftp://ftp.rsasecurity.com/pub/pkcs/pkcs-1/pkcs-1v2-1.pdf> and
-- <ftp://ftp.rsasecurity.com/pub/pkcs/ascii/pkcs-1.asc>) for 
-- further information.
-----------------------------------------------------------------------------

module Codec.ASN1.PKCS1v15(
   -- * Type Declarations
   DigestInfo(..),
   DigestAlgorithm,
   -- * Function Declarations
   encode, 
   decode,
   digestInfo,
   digestAlgorithm
   ) where

import Data.Maybe
import Codec.Utils (Octet)
import Codec.ASN1
import qualified Codec.ASN1.BER as BER
import Codec.ASN1.X509 (algorithmIdentifier,AlgorithmIdentifier)

-- | Not yet implemented.

encode :: [Octet] -> [Octet]

encode xs = error "tbd"

-- | Take an encoded message and return the decoded message provided all the
--   conditions in the specification are met.

decode :: [Octet] -> Maybe [Octet]
decode encoded =
   if decodeError 
      then Nothing
      else (Just m)
   where  
      (x0,t0) = splitAt 1 encoded
      (x1,t1) = splitAt 1 t0
      (ps,t2) = span (==0xff) t1
      (x3,m) = splitAt 1 t2
      decodeError = 
         and [
            x0 /= [0x00], 
            x1 /= [0x02], 
            x3 /= [0x00],
            length ps < 8
         ]

{-
DigestInfo ::= SEQUENCE {
   digestAlgorithm DigestAlgorithm,
   digest OCTET STRING
}
-}

digestInfo =
   "DigestInfo" ::=
      AbsSeq Universal 16 Implicit [
         Regular (Just "digestAlgorithm" :>: (Nothing :@:
   digestAlgorithm)),
         Regular (Just "digest"          :>: (Nothing :@:
   absOctetString))
      ]

data DigestInfo =
   DigestInfo {
      digestAlgorithm1 :: DigestAlgorithm,
      digest :: OctetString
      }
   deriving (Eq,Show)

instance BER.Encode DigestInfo where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = BER.encodedDefComps x
         return $
            DigestInfo {
               digestAlgorithm1 = fromJust $ BER.decode (as!!0) (bs!!0),
               digest = fromJust $ BER.decode (as!!1) (bs!!1)
            }

digestAlgorithm =
   modName "DigestAlgorithm" algorithmIdentifier

type DigestAlgorithm = AlgorithmIdentifier
