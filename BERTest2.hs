module Main(main) where

import Data.Char
import Data.Maybe
import Control.Monad.Error
import Control.Monad.State
import Language.ASN1.BER
import Language.ASN1
import Language.ASN1.X509
import Language.ASN1.InformationFramework(
   generalNames,
   GeneralNames,
   rdnSequence,
   RDNSequence(..),
   GeneralName(..),
   GeneralNames(..),
   Name(..)
   )
import Language.ASN1.X509.AttributeCertificateDefinitions (
   AttributeCertificate,
   attributeCertificate,
   Holder(..),
   holder,
   holder',
   HolderGeneralNames(..),
   holderGeneralNames,
   AttCertIssuer(..),
   attCertIssuer,
   IssuerSerial(..),
   issuerSerial,
   Attribute(..),
   attribute,
   AttributeValue(..)
   )
import Test.HUnit
import System.IO
import System.Environment
import System.Console.GetOpt
-- import Codec.Utils
import Language.ASN1.TLV
import NewBinary.Binary

expectSuccess testName asnType berValue expectedAbsValue =
   TestCase $
      do (w,x) <- typeCheck' asnType berValue
         let (_ ::= c) = w
             d = decode c (Just x)
             (Just y) = d
         assertEqual testName expectedAbsValue y

expectFailure testName asnType berValue expectedError =
   TestCase $
      do x <- (do y <- typeCheck' asnType berValue
                  return "Unexpected successful typechecking")
              `catchError` (\e -> return $ show e)
         assertEqual testName x expectedError

testHolder=
   Constructed Universal 16 56 [
      Constructed Context 1 54 [
         Constructed Context 4 52 [
            Constructed Universal 16 50 [
               Constructed Universal 17 11 [
                  Constructed Universal 16 9 [
                     Primitive Universal 6 3 [85,4,6],
                     Primitive Universal 19 2 [85,75]
                  ]
               ],
               Constructed Universal 17 17 [
                  Constructed Universal 16 15 [
                     Primitive Universal 6 3 [85,4,7],
                     Primitive Universal 19 8 [75,105,110,103,115,116,111,110]
                  ]
               ],
               Constructed Universal 17 16 [
                  Constructed Universal 16 14 [
                     Primitive Universal 6 3 [85,4,3],
                     Primitive Universal 19 7 [68,111,109,105,110,105,99]
                  ]
               ]
            ]
         ]
      ]
   ]

decodedHolder = 
   Holder {
      entityName = Just (
         HolderGeneralNames (
            decodedGNs
         )
      )
   }

tHolder = 
   expectSuccess "Holder" holder' testHolder decodedHolder

testGNs =
   Constructed Universal 16 54 [
      Constructed Context 4 52 [
         Constructed Universal 16 50 [
            Constructed Universal 17 11 [
               Constructed Universal 16 9 [
                  Primitive Universal 6 3 [85,4,6],
                  Primitive Universal 19 2 [85,75]
               ]
            ],
            Constructed Universal 17 17 [
               Constructed Universal 16 15 [
                  Primitive Universal 6 3 [85,4,7],
                  Primitive Universal 19 8 [75,105,110,103,115,116,111,110]
               ]
            ],
            Constructed Universal 17 16 [
               Constructed Universal 16 14 [
                  Primitive Universal 6 3 [85,4,3],
                  Primitive Universal 19 7 [68,111,109,105,110,105,99]
               ]
            ]
         ]
      ]
   ]

decodedGNs =
   GeneralNames [
      DirectoryName (
         Name (
            RDNSequence [
               RelativeDistinguishedName (
                  SetOf [
                     AttributeTypeAndValue {
                        type1 = OID [2,5,4,6], 
                        value = PS (PrintableString "UK")
                     }
                  ]
               ),
               RelativeDistinguishedName (
                  SetOf [
                     AttributeTypeAndValue {
                        type1 = OID [2,5,4,7], 
                        value = PS (PrintableString "Kingston")
                     }
                  ]
               ),
               RelativeDistinguishedName (
                  SetOf [
                     AttributeTypeAndValue {
                        type1 = OID [2,5,4,3], 
                        value = PS (PrintableString "Dominic")
                     }
                  ]
               )
            ]
         )
      )
   ]

foo =
   do (w,x) <- typeCheck' generalNames testGNs
      putStrLn (show x)
      putStrLn (show w)

tGeneralNames = 
   expectSuccess "GeneralNames" generalNames testGNs decodedGNs

testRDNS =
   Constructed Universal 16 50 [
      Constructed Universal 17 11 [
         Constructed Universal 16 9 [
            Primitive Universal 6 3 [85,4,6],
            Primitive Universal 19 2 [85,75]
         ]
      ],
      Constructed Universal 17 17 [
         Constructed Universal 16 15 [
            Primitive Universal 6 3 [85,4,7],
            Primitive Universal 19 8 [75,105,110,103,115,116,111,110]
         ]
      ],
      Constructed Universal 17 16 [
         Constructed Universal 16 14 [
            Primitive Universal 6 3 [85,4,3],
            Primitive Universal 19 7 [68,111,109,105,110,105,99]
         ]
      ]
   ]

decodedRDNS =
   RDNSequence [
      RelativeDistinguishedName (
         SetOf [
            AttributeTypeAndValue {
               type1 = OID [2,5,4,6], 
               value = PS (PrintableString "UK")
            }
         ]
      ),
      RelativeDistinguishedName (
         SetOf [
            AttributeTypeAndValue {
               type1 = OID [2,5,4,7], 
               value = PS (PrintableString "Kingston")
            }
         ]
      ),
      RelativeDistinguishedName (
         SetOf [
            AttributeTypeAndValue {
               type1 = OID [2,5,4,3], 
               value = PS (PrintableString "Dominic")
            }
         ]
      )
   ]

tRDNSequence = 
   expectSuccess "RDNSequence" rdnSequence testRDNS decodedRDNS

testHGNs =
   Constructed Context 1 17 [
      Constructed Context 4 15 [
         Constructed Universal 16 13 [
            Constructed Universal 17 11 [
               Constructed Universal 16 9 [
                  Primitive Universal 6 3 [85,4,6],
                  Primitive Universal 19 2 [85,75]
               ]
            ]
         ]
      ]
   ]

testHGNs' =
   Constructed Context 1 54 [
      Constructed Context 4 52 [
         Constructed Universal 16 50 [
            Constructed Universal 17 11 [
               Constructed Universal 16 9 [
                  Primitive Universal 6 3 [85,4,6],
                  Primitive Universal 19 2 [85,75]
               ]
            ],
            Constructed Universal 17 17 [
               Constructed Universal 16 15 [
                  Primitive Universal 6 3 [85,4,7],
                  Primitive Universal 19 8 [75,105,110,103,115,116,111,110]
               ]
            ],
            Constructed Universal 17 16 [
               Constructed Universal 16 14 [
                  Primitive Universal 6 3 [85,4,3],
                  Primitive Universal 19 7 [68,111,109,105,110,105,99]
               ]
            ]
         ]
      ]
   ]

decodedHGNs =
   HolderGeneralNames (
      GeneralNames [
         DirectoryName (
            Name (
               RDNSequence [
                  RelativeDistinguishedName (
                     SetOf [
                        AttributeTypeAndValue {
                           type1 = OID [2,5,4,6], 
                           value = PS (PrintableString "UK")
                        }
                     ]
                  )
               ]
            )
         )
      ]
   )

tHGNs = 
   expectSuccess "HGNs" holderGeneralNames testHGNs decodedHGNs

decodedHGNs' = 
   HolderGeneralNames (
            decodedGNs
   )

tHGNs' = 
   expectSuccess "HGNs'" holderGeneralNames testHGNs' decodedHGNs'

testACI =
   Constructed Context 0 124 [
      Constructed Universal 16 63 [
         Constructed Context 4 61 [
            Constructed Universal 16 59 [
               Constructed Universal 17 11 [
                  Constructed Universal 16 9 [
                     Primitive Universal 6 3 [85,4,6],
                     Primitive Universal 19 2 [71,66]
                  ]
               ],
               Constructed Universal 17 15 [
                  Constructed Universal 16 13 [
                     Primitive Universal 6 3 [85,4,10],
                     Primitive Universal 19 6 [80,69,82,77,73,83]
                  ]
               ],
               Constructed Universal 17 27 [
                  Constructed Universal 16 25 [
                     Primitive Universal 6 3 [85,4,3],
                     Primitive Universal 19 18 [
                        65,32,80,101,114,109,105,115,32,84,101,115,
                        116,32,85,115,101,114
                     ]
                  ]
               ]
            ]
         ]
      ],
      Constructed Context 0 57 [
         Constructed Universal 16 52 [
            Constructed Context 4 50 [
               Constructed Universal 16 48 [
                  Constructed Universal 17 11 [
                     Constructed Universal 16 9 [
                        Primitive Universal 6 3 [85,4,6],
                        Primitive Universal 19 2 [71,66]
                     ]
                  ],
                  Constructed Universal 17 15 [
                     Constructed Universal 16 13 [
                        Primitive Universal 6 3 [85,4,10],
                        Primitive Universal 19 6 [80,69,82,77,73,83]
                     ]
                  ],
                  Constructed Universal 17 16 [
                     Constructed Universal 16 14 [
                        Primitive Universal 6 3 [85,4,3],
                        Primitive Universal 19 7 [82,111,111,116,32,67,65]
                     ]
                  ]
               ]
            ]
         ],
         Primitive Universal 2 1 [3]
      ]
   ]

decodedACI =
   AttCertIssuer {
      issuerName = Just (
         GeneralNames [
            DirectoryName (
               Name (
                  RDNSequence [
                     RelativeDistinguishedName (
                        SetOf [
                           AttributeTypeAndValue {
                              type1 = OID [2,5,4,6], 
                              value = PS (PrintableString "GB")
                           }
                        ]
                     ),
                     RelativeDistinguishedName (
                        SetOf [
                           AttributeTypeAndValue {
                              type1 = OID [2,5,4,10], 
                              value = PS (PrintableString "PERMIS")
                           }
                        ]
                     ),
                     RelativeDistinguishedName (
                        SetOf [
                           AttributeTypeAndValue {
                              type1 = OID [2,5,4,3], 
                              value = PS (PrintableString "A Permis Test User")
                           }
                        ]
                     )
                  ]
               )
            )
         ]
      ),
      baseCertificateID = Just (
         IssuerSerial {
            issuer1 = GeneralNames [
               DirectoryName (
                  Name (
                     RDNSequence [
                        RelativeDistinguishedName (
                           SetOf [
                              AttributeTypeAndValue {
                                 type1 = OID [2,5,4,6], 
                                 value = PS (PrintableString "GB")
                              }
                           ]
                        ),
                        RelativeDistinguishedName (
                           SetOf [
                              AttributeTypeAndValue {
                                 type1 = OID [2,5,4,10], 
                                 value = PS (PrintableString "PERMIS")
                              }
                           ]
                        ),
                        RelativeDistinguishedName (
                           SetOf [
                              AttributeTypeAndValue {
                                 type1 = OID [2,5,4,3], 
                                 value = PS (PrintableString "Root CA")
                              }
                           ]
                        )
                     ]
                  )
               )
            ], 
            serial = 3, 
            issuerID = Nothing
         }
      )
   }

tACI = 
   expectSuccess "ACI" attCertIssuer testACI decodedACI

testACI1 =
   Constructed Context 0 124 [
      Constructed Universal 16 63 [
         Constructed Context 4 61 [
            Constructed Universal 16 59 [
               Constructed Universal 17 11 [
                  Constructed Universal 16 9 [
                     Primitive Universal 6 3 [85,4,6],
                     Primitive Universal 19 2 [71,66]
                  ]
               ]
            ]
         ]
      ],
      Constructed Context 0 57 [
         Constructed Universal 16 52 [
            Constructed Context 4 50 [
               Constructed Universal 16 48 [
                  Constructed Universal 17 11 [
                     Constructed Universal 16 9 [
                        Primitive Universal 6 3 [85,4,6],
                        Primitive Universal 19 2 [71,66]
                     ]
                  ]
               ]
            ]
         ],
         Primitive Universal 2 1 [3]
      ]
   ]

decodedACI1 = 
   AttCertIssuer {
      issuerName = Just (
         GeneralNames [
            DirectoryName (
               Name (
                  RDNSequence [
                     RelativeDistinguishedName (
                        SetOf [
                           AttributeTypeAndValue {
                              type1 = OID [2,5,4,6], 
                              value = PS (PrintableString "GB")
                           }
                        ]
                     )
                  ]
               )
            )
         ]
      ), 
      baseCertificateID = Just (
         IssuerSerial {
            issuer1 = GeneralNames [
               DirectoryName (
                  Name (
                     RDNSequence [
                        RelativeDistinguishedName (
                           SetOf [
                              AttributeTypeAndValue {
                                 type1 = OID [2,5,4,6], 
                                 value = PS (PrintableString "GB")
                              }
                           ]
                        )
                     ]
                  )
               )
            ], 
            serial = 3, 
            issuerID = Nothing
         }
      )
   }

tACI1 = 
   expectSuccess "ACI1" attCertIssuer testACI1 decodedACI1


testACI2 =
   Constructed Context 0 124 [
      Constructed Context 0 57 [
         Constructed Universal 16 52 [
            Constructed Context 4 50 [
               Constructed Universal 16 48 [
                  Constructed Universal 17 11 [
                     Constructed Universal 16 9 [
                        Primitive Universal 6 3 [85,4,6],
                        Primitive Universal 19 2 [71,66]
                     ]
                  ]
               ]
            ]
         ],
         Primitive Universal 2 1 [3]
      ]
   ]

decodedACI2 = 
   AttCertIssuer {
      issuerName = Nothing, 
      baseCertificateID = Just (
         IssuerSerial {
            issuer1 = GeneralNames [
               DirectoryName (
                  Name (
                     RDNSequence [
                        RelativeDistinguishedName (
                           SetOf [
                              AttributeTypeAndValue {
                                 type1 = OID [2,5,4,6], 
                                 value = PS (PrintableString "GB")
                              }
                           ]
                        )
                     ]
                  )
               )
            ],
            serial = 3, 
            issuerID = Nothing
         }
      )
   }

tACI2 = 
   expectSuccess "ACI2" attCertIssuer testACI2 decodedACI2

testIssuerSerial =
   Constructed Universal 16 57 [
      Constructed Universal 16 52 [
         Constructed Context 4 50 [
            Constructed Universal 16 48 [
               Constructed Universal 17 11 [
                  Constructed Universal 16 9 [
                     Primitive Universal 6 3 [85,4,6],
                     Primitive Universal 19 2 [71,66]
                  ]
               ]
            ]
         ]
      ],
      Primitive Universal 2 1 [3]
   ]

decodedIssuerSerial =
   IssuerSerial {
      issuer1 = GeneralNames [
         DirectoryName (
            Name (
               RDNSequence [
                  RelativeDistinguishedName (
                     SetOf [
                        AttributeTypeAndValue {
                           type1 = OID [2,5,4,6], 
                           value = PS (PrintableString "GB")
                        }
                     ]
                  )
               ]
            )
         )
      ], 
      serial = 3, 
      issuerID = Nothing
   }

tIssuerSerial = 
   expectSuccess "IssuerSerial" issuerSerial testIssuerSerial decodedIssuerSerial

setOfAny = [
   0x30,0x17,0x06,0x0A,0x09,0x92,0x26,0x89,
   0x93,0xF2,0x2C,0x64,0x01,0x01,0x31,0x09,
   0x13,0x07,0x44,0x6F,0x6D,0x69,0x6E,0x69,
   0x63
   ]

decodedSetOfAny =
   Attribute {
      attributeType = OID [0,9,2342,19200300,100,1,1], 
      attributeValues = SetOf [AVPS (PrintableString "Dominic")]
   }

tSetOfAny = 
   let (_,e) = tlv (map fromInteger setOfAny) in
      expectSuccess "SetOfAny" attribute e decodedSetOfAny

typeCheck' :: TypeDefn -> Encoding -> IO (TypeDefn,Defaulted)

{-
typeCheck' a b =
   do ((q,r),_) <- runStateT (tc a b) []
      return (q,r)
-}

typeCheck' = typeCheck

{-
TextBook = SEQUENCE {
   author         PrintableString,
   citationType   OID,
   reference      ANY DEFINED BY citationType
   }
-}

textBook =
   "TextBook" ::=
      AbsSeq Universal 16 Implicit
         [Regular (Just "author" :>: (Nothing :@: absPrintableString)),
          Regular (Just "citationType"  :>: (Nothing :@: absOID)),
          AnyDefBy 1]

data TextBook =
   TextBook {
      author :: PrintableString,
      citationType :: OID,
      reference :: Reference
   }
   deriving (Eq,Show)

instance Encode TextBook where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            TextBook {
               author = fromJust $ decode (as!!0) (bs!!0),
               citationType = fromJust $ decode (as!!1) (bs!!1),
               reference = fromJust $ decode (as!!2) (bs!!2)
            }

data Reference = ReferencePS PrintableString
   deriving (Eq,Show)

instance Encode Reference where
   decode a@(AbsBasePrim _ _ AbsPrintableString) b =
      do x <- decode a b
         return (ReferencePS x)
   decode a b =
      error (show a ++ "\n" ++ show b)

encodedPrintableString1 =
   Primitive Universal 19 5 [104,101,108,108,111]

encodedPrintableString2 =
   Primitive Universal 19 5 [105,101,108,108,111]

encodedOID1 = Primitive Universal 6 3 [85,4,7]

encodedTextBook2 =
   Constructed Universal 16 13 [
      encodedPrintableString1,
      encodedOID1,
      encodedPrintableString2
   ]

decodedTextBook =
   TextBook {
      author = PrintableString "hello", 
      citationType = OID [2,5,4,7], 
      reference = ReferencePS (PrintableString "iello")
   }

tTextBook = 
   expectSuccess "TextBook" textBook encodedTextBook2 decodedTextBook

{-
CollectionEntry = SEQUENCE
   {
   entry              TextBook,
   category           PrintableString,
   catagoriser        PrintableString,
   catType            OID,
   catNumber          ANY DEFINED BY catType
   }
-}

collection =
   "Collection" ::=
      AbsSeq Universal 16 Implicit [
         Regular (Just "entry" :>: (Nothing :@: textBook)),
         Regular (Just "category"  :>: (Nothing :@: absPrintableString)),
         Regular (Just "catagoriser" :>: (Nothing :@: absPrintableString)),
         Regular (Just "catType"  :>: (Nothing :@: absOID)),
         AnyDefBy 3
      ]

data Collection =
   Collection {
      entry :: TextBook,
      category :: PrintableString,
      categoriser :: PrintableString,
      catType :: OID,
      catNumber :: CatNumber
   }
   deriving (Eq,Show)

instance Encode Collection where
   decode a b =
      do x <- b
         let as = absSeqComponents a
             bs  = encodedDefComps x
         return $
            Collection {
               entry = fromJust $ decode (as!!0) (bs!!0),
               category = fromJust $ decode (as!!1) (bs!!1),
               categoriser = fromJust $ decode (as!!2) (bs!!2),
               catType = fromJust $ decode (as!!3) (bs!!3),
               catNumber = fromJust $ decode (as!!4) (bs!!4)
            }

data CatNumber = CatNumberPS PrintableString
   deriving (Eq,Show)

instance Encode CatNumber where
   decode a@(AbsBasePrim _ _ AbsPrintableString) b =
      do x <- decode a b
         return (CatNumberPS x)
   decode a b =
      error (show a ++ "\n" ++ show b)

encodedCollection = 
   Constructed Universal 16 30 [
      encodedTextBook2,
      encodedPrintableString2,
      encodedPrintableString2,
      encodedOID1,
      encodedPrintableString1
   ]

decodedCollection =
   Collection {
      entry = TextBook {
         author = PrintableString "hello", 
         citationType = OID [2,5,4,7], 
         reference = ReferencePS (PrintableString "iello")
      }, 
      category = PrintableString "iello", 
      categoriser = PrintableString "iello", 
      catType = OID [2,5,4,7], 
      catNumber = CatNumberPS (PrintableString "hello")
   }

tCollection = 
   expectSuccess "Collection" collection encodedCollection decodedCollection
      
tests =
   TestList [
   tRDNSequence, tGeneralNames, tHolder, tHGNs,
   tHGNs', tACI, tACI1, tACI2,
   tIssuerSerial, tSetOfAny, tTextBook, tCollection
   ]

main = runTestTT tests

