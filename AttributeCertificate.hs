module Main(main) where

import Data.Char
import Data.Maybe
import Control.Monad.Error
import Control.Monad.State
import Codec.ASN1.BER
import Codec.ASN1
import Codec.ASN1.X509
import Codec.ASN1.InformationFramework
import Codec.ASN1.X509.AttributeCertificateDefinitions
import Test.HUnit
import System.IO
import System.Environment
import System.Console.GetOpt
import Codec.Utils
import Codec.ASN1.TLV
import NewBinary.Binary
import Text.PrettyPrint
import Codec.Text.Raw

instance PP AttributeCertificate where
   pp ac =
      (label' "AttributeCertificateInfo". pp . attributeCertificateInfo1 $ ac)
      $$
      (label' "AlgorithmIdentifier" . pp . algorithmIdentifier2 $ ac)
      $$
      (label' "Encrypted" . pp . encrypted $ ac)

instance PP AttributeCertificateInfo where
   pp aci =
      (label "Version" . pp . version1 $ aci)
      $$
      (label' "Holder" . pp . holder1 $ aci)
      $$
      (label' "AttCertIssuer" . pp . issuer2 $ aci)
      $$
      (label' "AlgorithmIdentifier" . pp . signature1 $ aci)
      $$
      (label' "CertificateSerialNumber" . pp . serialNumber1 $ aci)
      $$
      (label' "CertificateValidity" . pp . attrCertValidityPeriod $ aci)
      $$
      (label' "Attributes" . pp . attributes $ aci)

label :: String -> Doc -> Doc
label s d = text s <> colon <> space <> d

hangingLabel :: String -> Int -> Doc -> Doc
hangingLabel s n d = hang (text s <> colon <> space) n d

label' s d = hangingLabel s 3 d

class PP a where
   pp :: a -> Doc

instance PP GeneralName where
  pp gn =
     case gn of
        Rfc822Name x -> text "Rfc822Name"
        DNSName x -> text "DNSName"
        DirectoryName x -> pp x
        UnifromResourceIdentifier x -> text "UniformResourceIdentifier"
        IPAddress x -> text "IPAddress"
        RegisteredID x -> text "RegisteredID"

instance PP a => PP [a] where
   pp xs = vcat (map pp xs)

instance PP a => PP (Maybe a) where
   pp Nothing = text "Nothing"
   pp (Just x) = pp x

instance PP Holder where
   pp = pp . entityName 

instance PP AttCertIssuer where
   pp aci = 
      (label "IssuerName" . pp . issuerName $ aci)
      $$
      (label' "BaseCertificateID" . pp . baseCertificateID $ aci)

instance PP IssuerSerial where
   pp is = 
      (label "Issuer" . pp . issuer1 $ is)
      $$
      (label "CertificateSerialNumber" . pp . serial $ is)

instance PP AlgorithmIdentifier where
   pp ai = 
      (label "Algorithm" . pp . algorithm1 $ ai)
      $$
      (label "Parameters" . pp . parameters1 $ ai)

instance PP NULL where
   pp _ = text "NULL"
   
instance PP Integer where
   pp = integer

instance PP BitString where
   pp (BitString bs) = hexdump 16 bs

instance PP HolderGeneralNames where
   pp (HolderGeneralNames x) = pp x

instance PP GeneralNames where
   pp (GeneralNames xs) = pp xs

instance PP VisibleString where
   pp (VisibleString x) = text x

instance PP PrintableString where
   pp (PrintableString x) = text x

instance PP IA5String where
   pp (IA5String x) = text x

instance PP DirectoryString where
   pp (VS x) = pp x
   pp (PS x) = pp x
   pp (IA x) = pp x

instance PP AttributeTypeAndValue where
   pp x =
      (pp . type1 $ x) <> space <> (pp . value $ x)   

instance PP Attribute where
   pp x =
      (pp . attributeType $ x) <> space <> (pp . attributeValues $ x)

instance PP AttributeValue where
   pp (AVPS x) = pp x

instance PP OID where
   pp x = text . show $ x

instance PP a => PP (SetOf a) where
   pp (SetOf x) = pp x

instance PP RelativeDistinguishedName where
   pp (RelativeDistinguishedName x) = pp x

instance PP RDNSequence where
   pp (RDNSequence x) = pp x

instance PP Name where
   pp (Name x) = pp x

instance PP AttCertValidityPeriod where
   pp x = 
      (label "NotBeforeTime" . pp . notBeforeTime $ x)
      $$
      (label "NotAfterTime" . pp . notAfterTime $ x)

instance PP GeneralizedTime where
   pp (GeneralizedTime x) = pp x

test1 fileName =
   do h   <- openFile fileName ReadMode
      bin <- openBinIO_ h
      (l,x) <- tlvIO bin
      (w,y) <- typeCheck attributeCertificate x
      let (_ ::= c) = w
      let d = (decode c (Just y))::(Maybe AttributeCertificate)
      putStrLn (render . pp . fromJust $ d)
      putStrLn "Success"

main =
   do progName <- getProgName
      args <- getArgs
      if length args /= 1
         then putStrLn ("Usage: " ++ progName ++ " <fileName>")
         else test1 (args!!0)
