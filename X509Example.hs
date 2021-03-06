module Main(main) where

import System.IO
import System.Environment
import Control.Monad.Error
import Data.Maybe
import Data.List
import Numeric
import NewBinary.Binary
import Language.ASN1.BER
import Language.ASN1
import Language.ASN1.TLV
import Language.ASN1.X509
import Language.ASN1.Utils
import Text.PrettyPrint
import Control.Monad.State

pp :: SignedCertificate -> RSAPublicKey -> String
pp sc rsapk = 
   render (
      ppLabelString "Version" (show (version3 (certificate1 sc)))
      $$
      ppLabelString "Serial Number" (show (serialNumber (certificate1 sc)))
      $$
      ppLabelDoc "Algorithm Identifier" algid
      $$
      ppLabelDoc "Issuer" iss
      $$
      ppLabelDoc "Validity" valid
      $$
      ppLabelDoc "Subject" sub
      $$
      ppLabelDoc "Subject Public Key Info" kk
   )
   where
      algid = 
         ppLabelString "Algorithm" 
                       (show (algorithm1 (signature (certificate1 sc))))
         $$
         ppLabelString "Parameters"
                        (show (parameters1 (signature (certificate1 sc))))
      iss = vcat (rdns issuer)
      sub = vcat (rdns subject)
      rdns select = (
         (map (\x -> (text (show (fst x)) <> 
                      space <> 
                      text (unDirectoryString (snd x))))) .
         (map (\x -> (type1 (head x),value (head x)))) .
         (map unSetOf) .
         (map unRelativeDistinguishedName) .
         unName .
         select .
         certificate1
         ) sc
      valid = 
         ppLabelString "NotBefore" nb
         $$
         ppLabelString "NotAfter" na
      nb = unVisibleString (unTime (notBefore (validity1 (certificate1 sc))))
      na = unVisibleString (unTime (notAfter (validity1 (certificate1 sc))))
      ki = subjectPublicKeyInfo2 (certificate1 sc)
      al = algorithm2 ki
      kj = subjectPublicKeyInfo1 ki
      algid1 = 
         ppLabelString "Algorithm" (show (algorithm1 al))
         $$
         ppLabelString "Parameters" (show (parameters1 al))
      kk = ppLabelDoc "Algorithm" algid1
           $$
           ppLabelDoc "Subject Public Key Info" spki
      spki = mod $$ exp
      exp  = ppLabelString "Exponent" (show (publicExponent1 rsapk))
      bar  = map (map sh) (split 16 (toOctets 256 (modulus1 rsapk)))
      sh x | x < 16    = showHex x "0"
           | otherwise = showHex x ""
      split :: Int -> [a] -> [[a]]
      split n xs = unfoldr (g n) xs
      g :: Int -> [a] -> Maybe ([a],[a])
      g n y 
         | length y == 0 = Nothing
         | otherwise     = Just (splitAt n y)
      mods1 :: [[Doc]]
      mods1 = map (intersperse colon) (map (map text) bar)
      mods2 :: [Doc]
      mods2 = map hcat mods1
      mod = ppLabelDoc "Modulus" (vcat mods2)

ppLabelString :: String -> String -> Doc
ppLabelString l x = 
   text l <> colon <> space <> (text x)

ppLabelDoc :: String -> Doc -> Doc
ppLabelDoc l d = 
   text l <> colon
   $$
   nest 3 d

test fileName = 
   do h   <- openFile fileName ReadMode
      bin <- openBinIO_ h
      (l,x) <- tlvIO bin
      (w,y) <- typeCheck signedCertificate x
      let (_ ::= c) = w
      let d = (decode c (Just y))::(Maybe SignedCertificate)
      let d1 = certificate1 (fromJust d)
      let d2 = subjectPublicKeyInfo2 d1
      let d3 = subjectPublicKeyInfo1 d2
      let (BitString e) = d3
      let (l',x') = tlv e
      (w',y') <- typeCheck rsaPublicKey x'
      let (_ ::= r) = w'
      let s = (decode r (Just y'))::(Maybe RSAPublicKey)
      putStrLn (pp (fromJust d) (fromJust s))

main = 
   do progName <- getProgName
      args <- getArgs
      if length args /= 1
         then putStrLn ("Usage: " ++ progName ++ " <fileName>")
         else test (args!!0)
