-----------------------------------------------------------------------------
-- |
-- Module      :  Language.ASN1.X509.InformationFramework
-- Copyright   :  (c) Dominic Steinitz 2006 - 2007
-- License     :  BSD3
-- 
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Definitions to allow the typechecking of (BER) encodings of definitions from
-- AttributeCertificateDefinitions {joint-iso-itu-t ds(5) module(1)
-- attributeCertificateDefinitions(32) 5}
-- and 
-- functions to extract information from encodings of them.
-- 
-- See <http://www.itu.int/ITU-T/asn1/database/itu-t/x/x509/2005/AttributeCertificateDefinitions.html>
--
-----------------------------------------------------------------------------

module Language.ASN1.X509.AttributeCertificateDefinitions (
-- * Type declarations
   AttributeCertificate(..),
   AttributeCertificateInfo(..),
   Holder(..),
   HolderGeneralNames(..),
   AttCertIssuer(..),
   IssuerSerial(..),
   Attribute(..),
   AttributeValue(..),
   AttCertValidityPeriod(..),
   GeneralizedTime(..),
-- * Function declarations
   attributeCertificate,
   holder,
   holder',
   holderGeneralNames,
   attCertIssuer,
   issuerSerial,
   attribute
   ) where

import Language.ASN1
import Language.ASN1.BER
import Data.Maybe(
   fromJust
   )
import Language.ASN1.X509 (
   algorithmIdentifier,
   AlgorithmIdentifier
   )
import Language.ASN1.InformationFramework (
   generalNames,
   GeneralNames
   )

{-
AttributeCertificate ::= SIGNED {AttributeCertificateInfo}

AttributeCertificate ::= SEQUENCE {
   attributeCertificateInfo AttributeCertificateInfo,
   algorithmIdentifier      AlgorithmIdentifier,
   encrypted                BIT STRING
   }   

AttributeCertificateInfo ::= SEQUENCE {
   version                AttCertVersion, --version is v2
   holder                 Holder,
   issuer                 AttCertIssuer,
   signature              AlgorithmIdentifier,
   serialNumber           CertificateSerialNumber,
   attrCertValidityPeriod AttCertValidityPeriod,
   attributes             SEQUENCE OF Attribute,
   issuerUniqueID         UniqueIdentifier OPTIONAL,
   extensions             Extensions OPTIONAL
   }

AttCertVersion ::= INTEGER { v2(1) }
-}

attributeCertificate :: TypeDefn
attributeCertificate =
   "attributeCertificate" ::=
      AbsSeq Universal 16 Implicit
         [Regular (Nothing :>: (Nothing :@: attributeCertificateInfo)),
          Regular (Nothing :>: (Nothing :@: algorithmIdentifier)),
          Regular (Nothing :>: (Nothing :@: absBitString))]

attributeCertificateInfo :: TypeDefn
attributeCertificateInfo =
   "attributeCertificateInfo" ::=
       AbsSeq Universal 16 Implicit [
          Regular (Just "version" :>: (Nothing :@: version)),
          Regular (Just "holder"  :>: (Nothing :@: holder')),
          Regular (Just "issuer"  :>: (Nothing :@: attCertIssuer)),
          Regular (Just "signature" :>: 
             (Nothing :@: algorithmIdentifier)),
          Regular (Just "serialNumber" :>: 
             (Nothing :@: certificateSerialNumber)),
          Regular (Just "attrCertValidityPeriod" :>: 
             (Nothing :@: attCertValidityPeriod)),
          Regular (Just "attributes" :>:
             (Nothing :@: (
                "SEQUENCE OF Attribute" ::=
                   AbsSeqOf Universal 16 Implicit attribute
                )
             )
          )
       ]

data AttributeCertificate =
   AttributeCertificate {
      attributeCertificateInfo1 :: AttributeCertificateInfo,
      algorithmIdentifier2 :: AlgorithmIdentifier,
      encrypted :: BitString
   } deriving (Eq,Show)      

instance Encode AttributeCertificate where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            AttributeCertificate {
               attributeCertificateInfo1 = fromJust $ decode (as!!0) (bs!!0),
               algorithmIdentifier2 = fromJust $ decode (as!!1) (bs!!1),
               encrypted = fromJust $ decode (as!!2) (bs!!2)
            }

data AttributeCertificateInfo =
   AttributeCertificateInfo {
      version1      :: Version,
      holder1       :: Holder,
      issuer2       :: AttCertIssuer,
      signature1    :: AlgorithmIdentifier,
      serialNumber1 :: CertificateSerialNumber,
      attrCertValidityPeriod ::  AttCertValidityPeriod,
      attributes    :: [Attribute]
   } deriving (Eq,Show)

instance Encode AttributeCertificateInfo where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            AttributeCertificateInfo {
               version1      = fromJust $ decode (as!!0) (bs!!0),
               holder1       = fromJust $ decode (as!!1) (bs!!1),
               issuer2       = fromJust $ decode (as!!2) (bs!!2),
               signature1    = fromJust $ decode (as!!3) (bs!!3),
               serialNumber1 = fromJust $ decode (as!!4) (bs!!4),
               attrCertValidityPeriod = fromJust $ decode (as!!5) (bs!!5),
               attributes    = fromJust $ decode (as!!6) (bs!!6)
            }

type Version = Integer

version = modName "Version" absInteger

{-
Holder ::= SEQUENCE {
   baseCertificateID [0] IssuerSerial OPTIONAL,
   -- the issuer and serial number of the holder's Public Key Certificate
   entityName [1] GeneralNames OPTIONAL,
   -- the name of the entity or role
   objectDigestInfo [2] ObjectDigestInfo OPTIONAL
   --used to directly authenticate the holder, e.g. an executable
   --at least one of baseCertificateID, entityName or objectDigestInfo
   -- shall be present
   }
-}

holder =
   "Holder" ::= 
      AbsSeq Universal 16 Implicit
         [Optional (Just "entityName" :>: (Just 1 :@: generalNames))]

holder' =
   "Holder" ::= 
      AbsSeq Universal 16 Implicit
         [Optional (Nothing :>: (Nothing :@: holderGeneralNames))]

{-
We don't handle IMPLICIT / EXPLICIT correctly on ComponentTypes of
SEQUENCE so we have to invent a new intermediate type to get over 
the problem here until it is fixed in the main ASN1 module.

HolderGeneralNames ::=
   [1] IMPLICIT GeneralNames
-}

holderGeneralNames = 
   "entityName" ::= AbsRef Context 1 Implicit generalNames

data HolderGeneralNames = 
   HolderGeneralNames GeneralNames
      deriving (Eq,Show)

instance Encode HolderGeneralNames where
   decode a b =
      do x <- decode a b
         return $ HolderGeneralNames x

data Holder =
   Holder {
      entityName :: Maybe HolderGeneralNames
   }
   deriving (Eq,Show)

instance Encode Holder where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            Holder {
               entityName = decode (as!!0) (bs!!0)
            }

{-
AttCertIssuer ::= [0] SEQUENCE {
   issuerName            GeneralNames     OPTIONAL,
   baseCertificateID [0] IssuerSerial     OPTIONAL,
   objectDigestInfo  [1] ObjectDigestInfo OPTIONAL 
   }
-- At least one component shall be present
   ( WITH COMPONENTS { ..., issuerName PRESENT } |
     WITH COMPONENTS { ..., baseCertificateID PRESENT } |
     WITH COMPONENTS { ..., objectDigestInfo PRESENT } )
-}

attCertIssuer :: TypeDefn
attCertIssuer =
   "attCertIssuer" ::=
      AbsSeq Context 0 Implicit
         [Optional (Just "issuerName" :>: 
             (Nothing :@: generalNames)),
          Optional (Just "baseCertificateID" :>:
             (Just 0 :@: issuerSerial))
{-
051218140100

For now. Since with the PERMIS attribute certificate, we know
that we will get an issuerName, we don't have to support this yet
and ObjectDigestInfo is a) more work and b) contains ENUMERATED
which we don't support yet even though it's not hard so to do.

          Optional (Just "objectDigestInfo" :>:
             (Just 1 :@: objectDigestInfo))
-}
      ]

data AttCertIssuer =
   AttCertIssuer {
      issuerName :: Maybe GeneralNames,
      baseCertificateID :: Maybe IssuerSerial
   }
   deriving (Eq,Show)

instance Encode AttCertIssuer where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            AttCertIssuer {
               issuerName = decode (as!!0) (bs!!0),
               baseCertificateID = decode (as!!1) (bs!!1)
            }

{-      
IssuerSerial ::= SEQUENCE {
   issuer    GeneralNames,
   serial    CertificateSerialNumber,
   issuerUID UniqueIdentifier OPTIONAL 
   }
-}

issuerSerial =
   "IssuerSerial" ::=
      AbsSeq Universal 16 Implicit [
         Regular  (Just "issuer"    :>: (Nothing :@: generalNames)),
         Regular  (Just "serial"    :>: (Nothing :@: certificateSerialNumber)),
         Optional (Just "issuerUID" :>: (Nothing :@: uniqueIdentifier))
      ]

data IssuerSerial =
   IssuerSerial {
      issuer1  :: GeneralNames,
      serial   :: CertificateSerialNumber,
      issuerID :: Maybe UniqueIdentifier
   }
   deriving (Eq,Show)

instance Encode IssuerSerial where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            IssuerSerial {
               issuer1  = fromJust $ decode (as!!0) (bs!!0),
               serial   = fromJust $ decode (as!!1) (bs!!1),
               issuerID = decode (as!!2) (bs!!2)
            }

{-
CertificateSerialNumber ::= INTEGER
-}

certificateSerialNumber =
   modName "CertificateSerialNumber" absInteger

type CertificateSerialNumber = Integer

{-
AttCertValidityPeriod ::= SEQUENCE {
   notBeforeTime GeneralizedTime,
   notAfterTime GeneralizedTime 
   }
-}

attCertValidityPeriod :: TypeDefn
attCertValidityPeriod =
   "Validity" ::=
      AbsSeq Universal 16 Implicit
         [Regular (Just "notBeforeTime"  :>: (Nothing :@: generalizedTime)),
          Regular (Just "notAfterTime"   :>: (Nothing :@: generalizedTime))]

data AttCertValidityPeriod =
   AttCertValidityPeriod {
      notBeforeTime :: GeneralizedTime,
      notAfterTime  :: GeneralizedTime
      }
   deriving (Eq,Show)

instance Encode AttCertValidityPeriod where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            AttCertValidityPeriod {
               notBeforeTime = fromJust $ decode (as!!0) (bs!!0),
               notAfterTime  = fromJust $ decode (as!!1) (bs!!1)
            }

{-
This is really from X.680.

GeneralizedTime ::= [UNIVERSAL 24] IMPLICIT VisibleString
-}

generalizedTime :: TypeDefn
generalizedTime =
   "Time" ::= AbsRef Universal 24 Implicit absVisibleString

data GeneralizedTime = GeneralizedTime VisibleString
   deriving (Eq,Show)

instance Encode GeneralizedTime where
   decode a b =
      do x <- decode a b
         return $ GeneralizedTime x

{-
This is really from

SelectedAttributeTypes {
   joint-iso-itu-t ds(5) module(1) selectedAttributeTypes (5) 4
   }

UniqueIdentifier ::= BIT STRING

WARNING: typechecking BIT STRING is a kludge and may not work for this.
-}

uniqueIdentifier =
   modName "UniqueIdentifier" absBitString

type UniqueIdentifier = BitString

{-
This is invalid ASN.1 even though it comes from
RFC 3281.

Attribute ::= SEQUENCE {
   type      AttributeType,
   values    SET OF AttributeValue
   -- at least one value is required
   }

AttributeType ::= OBJECT IDENTIFIER

AttributeValue ::= ANY DEFINED BY AttributeType

This is also invalid but it should be easy to support
typechecking of it.

Attribute ::= SEQUENCE {
   type  AttributeType,
   values SET OF ANY DEFINED BY type,
   -- at least one value is required
   }

The "real" definition is from

InformationFramework 
{joint-iso-itu-t(2) ds(5) module(1) informationFramework(1) 3}
has a different definition:

Attribute ::= SEQUENCE {
   type 
      ATTRIBUTE.&id({SupportedAttributes}),
   values
      SET SIZE (0..MAX) OF
         ATTRIBUTE.&Type({SupportedAttributes}{@type}),
   valuesWithContext
      SET SIZE (1..MAX) OF
         SEQUENCE {
            value ATTRIBUTE.&Type({SupportedAttributes}{@type}),
            contextList  SET SIZE (1..MAX) OF Context} OPTIONAL
   }

Thus we won't support valuesWithContext. Should they be present,
they will be ignored.
-}

{-
attribute :: TypeDefn
attribute =
   "Attribute" ::=
      AbsSeq Universal 16 Implicit
         [Regular (Just "type"  :>: (Nothing :@: absOID)),
          AnyDefBy 0]
-}

attribute :: TypeDefn
attribute =
   "Attribute" ::=
      AbsSeq Universal 16 Implicit [
         Regular (Just "type"  :>: (Nothing :@: absOID)),
         Regular (
            Just "values" :>: (
               Nothing :@: (
                  "SET OF AttributeValue" ::= 
                     AbsSetOf Universal 17 Implicit (
                        "ANY DEFINED BY type" ::= AbsAnyDefBy 0
                     )
               )
            )
         )
      ]

data Attribute =
   Attribute {
      attributeType   :: OID,
      attributeValues :: SetOf AttributeValue
   }
   deriving (Eq,Show)

instance Encode Attribute where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            Attribute {
               attributeType   = fromJust $ decode (as!!0) (bs!!0),
               attributeValues = fromJust $ decode (as!!1) (bs!!1)
            }

data AttributeValue = AVPS PrintableString
   deriving (Eq,Show)

instance Encode AttributeValue where
   decode a@(AbsBasePrim _ _ AbsPrintableString) b =
      do x <- decode a b
         return (AVPS x)
   decode a b =
      error (show a ++ "\n" ++ show b)

