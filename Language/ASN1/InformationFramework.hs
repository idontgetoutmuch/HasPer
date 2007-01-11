-----------------------------------------------------------------------------
-- |
-- Module      :  Language.ASN1.InformationFramework
-- Copyright   :  (c) Dominic Steinitz 2006
-- License     :  BSD3
-- 
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Definitions to allow the typechecking of (BER) encodings of definitions from
-- InformationFramework {joint-iso-itu-t(2) ds(5) module(1) informationFramework(1) 3}
-- and 
-- functions to extract information from encodings of them.
-- 
-- See <http://www.itu.int/ITU-T/asn1/database/itu-t/x/x501/2005/InformationFramework.html>
--
-----------------------------------------------------------------------------

module Language.ASN1.InformationFramework (
-- * Type declarations
   GeneralName(..),
   GeneralNames(..),
   Name(..),
   RDNSequence(..),
-- * Function declarations
   generalName,
   generalNames,
   name,
   rdnSequence,
   unRDNSequence
   ) where

import Language.ASN1
import Language.ASN1.BER
import Language.ASN1.X509 (
   relativeDistinguishedName,
   RelativeDistinguishedName
   )

{-
GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName

GeneralName ::= CHOICE {
   otherName                 [0] INSTANCE OF OTHER-NAME,
   rfc822Name                [1] IA5String,
   dNSName                   [2] IA5String,
   x400Address               [3] ORAddress,
   directoryName             [4] Name,
   ediPartyName              [5] EDIPartyName,
   uniformResourceIdentifier [6] IA5String,
   iPAddress                 [7] OCTET STRING,
   registeredID              [8] OBJECT IDENTIFIER
   }

-- naming data types 
Name ::= CHOICE { 
   -- only one possibility for now 
   rdnSequence RDNSequence
   }

RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
-}

generalName :: TypeDefn
generalName =
   "GeneralName" ::= 
      AbsChoice [
--          (Explicit, Just "otherName" :>: [0] INSTANCE OF OTHER-NAME),
         (Explicit, Just "rfc822Name" :>: (Just 1 :@: absIA5String)),
         (Explicit, Just "dNSName" :>: (Just 2 :@: absIA5String)),
--          (Explicit, Just "x400Address" :>: [3] ORAddress),
         (Explicit, Just "directoryName" :>: (Just 4 :@: name)),
--          (Explicit, Just "ediPartyName" :>: [5] :@: EDIPartyName),
         (Explicit, Just "uniformResourceIdentifier" :>: 
            (Just 6 :@: absIA5String)),
         (Explicit, Just "iPAddress" :>: (Just 7 :@: absOctetString)),
         (Explicit, Just "registeredID" :>: (Just 8 :@: absOID))
      ]

data GeneralName =
   Rfc822Name                IA5String   |
   DNSName                   IA5String   |
   DirectoryName             Name        |
   UnifromResourceIdentifier IA5String   |
   IPAddress                 OctetString |
   RegisteredID              OID
      deriving (Eq,Show)

instance Encode GeneralName where
   decode a b =
      do x <- b
         let t  = defaultedTagValue x
             bs = encodedDefComps x
             a' = absRefedType a
             b' = (encodedDefComps x)!! 0
         case t of
            1 -> do foo <- decode a' b'
                    return $ Rfc822Name foo
            2 -> do foo <- decode a' b'
                    return $ DNSName foo
            4 -> do foo <- decode a' b'
                    return $ DirectoryName foo
            6 -> do foo <- decode a' b'
                    return $ UnifromResourceIdentifier foo
            7 -> do foo <- decode a' b'
                    return $ IPAddress foo
            8 -> do foo <- decode a' b'
                    return $ RegisteredID foo

generalNames :: TypeDefn
generalNames = 
   "GeneralNames" ::= 
      AbsSeqOf Universal 16 Implicit generalName

data GeneralNames = GeneralNames [GeneralName]
   deriving (Eq,Show)

instance Encode GeneralNames where
   decode a b =
      do x <- decode a b
         return (GeneralNames x)

name :: TypeDefn
name =
   "Name" ::=
      AbsChoice [(Implicit,Just "rdnSequence" :>: (Nothing :@: rdnSequence))]

data Name= Name RDNSequence
   deriving (Eq,Show)

instance Encode Name where
   decode a b =
      do x <- b
         let t = defaultedTagValue x
         case t of
            16 -> do foo <- decode a b
                     return $ Name foo

rdnSequence :: TypeDefn
rdnSequence =
   "RDNSequence" ::=
      AbsSeqOf Universal 16 Implicit relativeDistinguishedName

data RDNSequence = RDNSequence [RelativeDistinguishedName]
   deriving (Eq,Show)

unRDNSequence :: RDNSequence -> [RelativeDistinguishedName]
unRDNSequence (RDNSequence x) = x

instance Encode RDNSequence where
   decode a b =
      do x <- decode a b
         return (RDNSequence x)

