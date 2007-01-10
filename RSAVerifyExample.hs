module Main(main) where

import System.IO
import Data.Char
import Data.List
import System.Environment
import System.Console.GetOpt
import Data.Maybe
import Codec.ASN1
import Codec.Utils
import Data.Digest.SHA1
import Codec.Encryption.RSA
import Codec.ASN1.TLV
import Codec.ASN1.X509
import Codec.ASN1.BER
import NewBinary.Binary
import qualified Codec.ASN1.PKCS1v15 as V15

verifyWith certFile plainTextFile signedFile = 
{-
certFile should contain an X.509 certificate.
-}
   do hcert   <- openFile certFile ReadMode
      hplain  <- openFile plainTextFile ReadMode
      hsign   <- openFile signedFile ReadMode
      ptext   <- hGetContents hplain
      psign   <- hGetContents hsign
      bin     <- openBinIO_ hcert
      (_,x)   <- tlvIO bin
{-
Typecheck this is really a signed certificate.
-}
      (w,sc) <- typeCheck signedCertificate x
{-
If it is then decode it and extract the bitstring containing the RSA
public key.
-}
      let (_ ::= c) = w
          d  = decode c (Just sc)
          d1 = certificate1 (fromJust d)
          d2 = subjectPublicKeyInfo2 d1
          d3 = subjectPublicKeyInfo1 d2
          (BitString e) = d3
          (_,x') = tlv e
{-
Typecheck this really is an RSA public key.
-}
      (w',rpk) <- typeCheck rsaPublicKey x'
{-
If it is then decode it and extract the modulus and the public
exponent.
-}
      let (_ ::= r) = w'
          s  = (decode r (Just rpk))
          n  = toOctets 256 $ modulus1 $ fromJust s 
          d  = toOctets 256 $ publicExponent1 $ fromJust s
{-
Decrypt the signature.
-}
          sd = decrypt (n,d) (map (fromIntegral . ord) psign)
          md = V15.decode sd
          di = fromJust md
          (l,v) = tlv $ di
      if md == Nothing 
         then error "Decryption error"
         else do (w'',w) <- typeCheck V15.digestInfo v
                 let (_ ::= d) = w''
                     e = decode d (Just w)
                 putStrLn (show (V15.digestAlgorithm1 (fromJust e)))
                 putStrLn ("Given digest:      " ++ (show (V15.digest (fromJust e))))
{-
Compute the hash of the plaintext file which the signature is
purported to have signed.
-}
                 let h  = hash $ map (fromIntegral . ord) ptext
                     g = OctetString h
                 putStrLn ("Calculated digest: " ++ (show g))
                 if (V15.digest (fromJust e) == g)
                    then putStrLn "Verified"
                    else putStrLn "Unable to verify"

main = do pn <- getProgName
          args <- getArgs
          (fs,ss) <- opts pn args
          let sfs        = sort fs
              (Cert e)   = sfs!!0
              (Input i)  = sfs!!1
              (Sig s)    = sfs!!2
          verifyWith e i s

data Flag = Cert String | Input String | Sig String 
   deriving (Show,Eq,Ord)

options = [
   Option ['e'] ["cert","certificate"]  (ReqArg Cert "CERT")
          "Certificate File",
   Option ['p'] ["plain","plaintext"]   (ReqArg Input "INPUT")
          "Plaintext File",
   Option ['s'] ["sig","signature"]     (ReqArg Sig "SIGNATURE")
          "Signature File"
   ]
    
opts :: String -> [String] -> IO ([Flag], [String])
opts progName argv = 
   case getOpt Permute options argv of
      (o,n,[]  ) -> 
         if length o == 3
            then return (o,n)
            else ioError (userError (usageInfo header options))
      (_,_,errs) -> 
         ioError (userError (concat errs ++ usageInfo header options))
      where header = "Usage: " ++ progName ++ " [OPTION...] files..."
