\section{Introduction}

Testing encoding for UNALIGNED PER

%if False

\begin{code}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -XFlexibleContexts
#-}

\end{code}

%endif

\begin{code}

module TestCTR where

import CTRestruct
import Text.PrettyPrint
import NewPretty
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.Strict.BitPut as BP
import Control.Monad.Error

import LatticeMod

import Test.QuickCheck
import Test.HUnit

import ASNTYPE
import ConstraintGeneration

import Language.ASN1(TagType(..), TagPlicity(..))

sc1 = UNION (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (251,255))))))
sc2 = UNION (IC (INTER (ATOM (E (V (R (270,273))))) (E (V (R (271,276))))))
sc3 = UNION (UC (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (259,262))))))
             (ATOM (E (V (R (251,255))))))


con1 = RE (UNION (IC (ATOM (E (V (R (250,253)))))))
con2 = RE (UNION (IC (ATOM (E (V (R (245,253)))))))
con3 = RE sc1
con32 = RE sc3
con4 = EXT sc1
con5 = EXTWITH sc1 sc2

-- String constraints
pac1 = UNION (UC (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,5)))))))))))))
             (ATOM (E (P (FR (RE (UNION (IC (ATOM (E (S (SV (VisibleString "dan")))))))))))))

pac2 = UNION (IC (INTER (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (8,8))))))))))))
             (E (P (FR (RE (UNION (IC (ATOM (E (S (SV (VisibleString "0123456789")))))))))))))

pac3 = UNION (IC (INTER (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (245,249))))))))))))
             (E (S (SV (VisibleString "adn"))))))

pac4 = UNION (UC (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,5)))))))))))))
             (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (7,10)))))))))))))

pac5 = UNION (IC (ATOM ((E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (3,3))))))))))))))

ns1 = RE (UNION (IC (ATOM ((E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,1)))))))))))))))

tester :: Either String (ExtResStringConstraint (ResStringConstraint VisibleString IntegerConstraint))
tester =  lLastApply (ExtResStringConstraint (ResStringConstraint (VisibleString "Dan")
            (IntegerConstraint 1 64)) top True) (Right (ExtResStringConstraint
            (ResStringConstraint top (IntegerConstraint 1 1)) top False))


dateCon = RE (UNION (IC (INTER (ATOM (E (SZ (SC (EXTWITH (UNION (IC (ATOM (E (V (R (8,8)))))))
                    (UNION (IC (ATOM (E (V (R (9,20))))))))))))
             (E (P (FR (RE (UNION (IC (ATOM (E (S (SV (VisibleString "0123456789"))))))))))))))

nameStringCon
    = RE (UNION (IC (INTER (ATOM (E (SZ (SC (EXT (UNION (IC (ATOM (E (V (R (1,64))))))))))))
             (E (P (FR (RE (UNION (UC
                            (UC (IC (ATOM (E (S (SV (VisibleString ['a'..'z']))))))
                                    (ATOM (E (S (SV (VisibleString ['A'..'Z']))))))
                                    (ATOM (E (S (SV (VisibleString "-."))))))))))))))

nameString
    = ConsT (BT VISIBLESTRING) nameStringCon


name = BT (SEQUENCE nameSeq)


nameSeq = Cons (CTMandatory (NamedType "givenName" nameString))
                (Cons (CTMandatory (NamedType "initial" (ConsT nameString ns1)))
                    (Cons (CTMandatory (NamedType "familyName"  nameString))
                        (Extens Nil)))

nameVal = VisibleString "John" :*: (VisibleString "P" :*: (VisibleString "Smith" :*: Empty))

cpac1 = [RE pac1]
cpac2 = [RE pac2]
cpac3 = [RE pac3]
cpac4 = [RE pac4]
cpac5 = [dateCon]



--Integer constraint generation
applycon1 :: Either [Char] IntegerConstraint
applycon1 = lRootIntCons top [con3, con1]

applycon2 :: Either [Char] ValidIntegerConstraint
applycon2 = lRootIntCons top [con3, con1]

applycon3 :: Either [Char] IntegerConstraint
applycon3 = lRootIntCons top [con32,con1]

applycon4 :: Either [Char] ValidIntegerConstraint
applycon4 = lRootIntCons top [con32,con1]


--Integer types

t1 = ConsT (BT INTEGER) con1
t2 = ConsT t1 con2
t3 = ConsT (ConsT (BT INTEGER) con2) con1
t4 = ConsT (BT INTEGER) con3
t5 = ConsT (BT INTEGER) con4
t6 = ConsT (BT INTEGER) con5
t7 = ConsT (ConsT (BT INTEGER) con5) con1

test1 = perEncode t1 [] 253
test2 = perEncode t2 [] 250
test3 = perEncode t3 [] 250
test4 = perEncode t4 [] 247
test5 = perEncode t5 [] 247
test6 = perEncode t6 [] 247
test7 = perEncode t6 [] 272
test8 = perEncode t6 [] 274
test9 = perEncode t7 [] 251
test10 = perEncode t7 [] 271

-- String types

--constrained
st1 = ConsT (BT VISIBLESTRING) (RE pac2)
st2 = ConsT (BT VISIBLESTRING) (RE pac4)
st3 = ConsT (BT VISIBLESTRING) dateCon
st4 = ConsT (BT VISIBLESTRING) nameStringCon

--unconstrained
ust1 = ConsT (BT NUMERICSTRING) (RE pac5)

testS1 = myTest st1 (VisibleString "19571111")
testS2 = myTest st3 (VisibleString "19571111")
testS3 = myTest st2 (VisibleString "Daniel")
testS4 = myTest st4 (VisibleString "Smith")
testS5 = myTest ust1 (NumericString "123")
testS6 = myTest ust1 (NumericString "dan")

-- BITSTRING
pac41 = UNION (UC (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,5)))))))))))))
             (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (7,10)))))))))))))
st5 = ConsT (BT (BITSTRING [])) (RE pac41)
st6 = ConsT (BT (BITSTRING [NB "A" 2, NB "B" 3])) (RE pac41)

testBS1 = myTest st5 (BitString [1,1,0,0,0,0,0])
testBS2 = myTest st6 (BitString [1,1,0,0,0,0,0,0,1,0,0,0])

sibDataVariableType =
   ConsT (BT (BITSTRING [])) (RE (UNION (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,214)))))))))))))))

sibDataVariableValue =
   BitString [1,1,1,1,1,1,1,1]

sibTest = myTest' sibDataVariableType sibDataVariableValue

incompleteSIBList = BT (SEQUENCEOF sibDataVariableType)

completeSIBListConstraint :: Constr [BitString]
completeSIBListConstraint = UNION (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,16)))))))))))))

completeSIBList = ConsT (BT (SEQUENCEOF sibDataVariableType)) (RE completeSIBListConstraint)

completeSIBListTest = lEncode completeSIBList [] (take 3 $ repeat (BitString [1,1,1,1,1,1,1,1]))

seqOfTest1 = lEncode (BT (SEQUENCEOF (BT INTEGER))) [] (take 1 $ repeat (Val 1))

-- OCTETSTRING
os41 = UNION (UC (IC (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (1,5)))))))))))))
             (ATOM (E (SZ (SC (RE (UNION (IC (ATOM (E (V (R (7,10)))))))))))))
os1 = ConsT (BT (OCTETSTRING)) (RE os41)

testOS1 = myTest os1 (OctetString [20,140,5,16,23,87,10])

-- SEQUENCE

testSeq1 = myTest name nameVal


-- CHOICE

axSeq = Cons (CTMandatory (NamedType "a" (ConsT (BT INTEGER) con1)))
                (Cons (CTMandatory (NamedType "b" (BT BOOLEAN)))
                    (Cons (CTMandatory (NamedType "c" (BT (CHOICE choice1))))
                        (Extens
                          (EAG eag1
                           (Extens (Cons (CTOptional (NamedType "i" (BT BMPSTRING)))
                                (Cons (CTOptional (NamedType "j" (BT PRINTABLESTRING)))
                                    Nil)))))))

choice1 = ChoiceOption (NamedType "d" (BT INTEGER))
            (ChoiceExt (ChoiceEAG
                            (ChoiceOption (NamedType "e" (BT BOOLEAN))
                                   (ChoiceOption (NamedType "f"  (BT IA5STRING))
                                          (ChoiceEAG (ChoiceExt NoChoice))))))


eag1 = Cons (CTMandatory (NamedType "g" (ConsT (BT NUMERICSTRING) (RE pac5))))
        (Cons (CTOptional (NamedType "h" (BT BOOLEAN))) Nil)


axVal = 253 :*:
        (True :*:
            ((NoValueC NoValue (ValueC True (NoValueC NoValue EmptyHL))) :*:
                    ((Just ((NumericString "123") :*: (Just True :*: Empty))) :*:
                        (Nothing :*: (Nothing :*: Empty)))))


testChoice1 = myTest (BT (SEQUENCE axSeq)) axVal



-- type inclusion tests
ti1 :: Either String IntegerConstraint
ti1 = lCalcE (C (Inc t1))

ti2 :: Either String IntegerConstraint
ti2 = lCalcE (C (Inc t6))
\end{code}


Examples from 13.6.1 of Dubuisson:

\begin{code}
dash  = ATOM (E (S (SV (PrintableString "-"))))
dot   = ATOM (E (S (SV (PrintableString "."))))
blank = ATOM (E (S (SV (PrintableString " "))))

morseChars = RE (UNION (UC (UC (IC dash) dot) blank))

morseAlphabet = ConsT (BT PRINTABLESTRING) morseChars

morse = ConsT (BT PRINTABLESTRING ) (RE (UNION (IC (ATOM ((E (P (FR morseChars))))))))

-- Note that the outer monad is BitGet and the inner monad is the Error

-- thereAndBack x = flip (BG.runBitGet . BP.runBitPut . bitPutify . encodeUInt ) (runErrorT decodeUInt) x

mySc1 = UNION (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (251,255))))))
mySc2 = UNION (IC (INTER (ATOM (E (V (R (270,273))))) (E (V (R (271,276))))))

myCon1 = RE (UNION (IC (ATOM (E (V (R (250,253)))))))
myCon2 = RE (UNION (IC (ATOM (E (V (R (245,253)))))))
myCon3 = RE mySc1
myCon4 = EXT mySc1
myCon5 = EXTWITH mySc1 mySc2

mt1 = ConsT (BT INTEGER) myCon1
mt2 = ConsT mt1 myCon2
mt3 = ConsT (ConsT (BT INTEGER) myCon2) myCon1
mt4 = ConsT (BT INTEGER) myCon3
mt5 = ConsT (BT INTEGER) myCon4
mt6 = ConsT (BT INTEGER) myCon5
mt7 = ConsT (ConsT (BT INTEGER) myCon5) myCon1

\end{code}

\subsection{SEQUENCE}

See Figure~\ref{sequenceTest1}.

\begin{code}

c1 = CTMandatory (NamedType "c1" (BT (TAGGED (Context,1,Explicit) (BT INTEGER))))
c2 = CTMandatory (NamedType "c2" (BT (TAGGED (Context,2,Explicit) (BT INTEGER))))

d1 = CTMandatory (NamedType "c1" (BT INTEGER))
d2 = CTMandatory (NamedType "c2" (BT INTEGER))

e1 = CTMandatory (NamedType "e1" tSequence1)
e2 = CTMandatory (NamedType "e2" tSequence1)


\end{code}

\begin{asn1}[caption={SEQUENCE Test 1},label=sequenceTest1]
SEQUENCE {c2 [2] EXPLICIT INTEGER,
          c1 [1] EXPLICIT INTEGER}
\end{asn1}

\begin{code}

tSequence1 = BT (SEQUENCE (Cons c2 (Cons c1 Nil)))
vSequence1 = (Val 3) :*: ((Val 5) :*: Empty)

tSequence2 = BT (SEQUENCE (Cons d2 (Cons d1 Nil)))

tSequence3 = BT (SEQUENCE (Cons e2 (Cons e1 Nil)))
vSequence3 = ((Val 2) :*: (Val 3 :*: Nil)) :*: (((Val 5) :*: ((Val 7) :*: Nil)) :*: Nil)


myTest t x =
   case lEncode t [] x of
      Left s  -> s
      Right m -> show m -- (B.unpack (BP.runBitPut m))

myTest' t x =
   case lEncode t [] x of
      Left s  -> error s
      Right m -> m

myTAB'' t x =
    case lEncode t [] x of
        Left s  -> error ("First " ++ s)
        Right y -> case BG.runBitGet (BP.runBitPut (bitPutify y)) (runErrorT (decode4 t [])) of
                      Left t -> error ("Second " ++ t)
                      Right z -> case z of
                                    Left e -> error ("Third " ++ (show e))
                                    Right v -> v

myTAB1 t x =
    case lEncode t [] x of
        Left s  -> error ("First " ++ s)
        Right y -> B.unpack (BP.runBitPut (bitPutify y))

instance Arbitrary InfInteger where
   arbitrary =
      frequency [
         (1,return NegInf),
         (2,liftM Val arbitrary),
         (1,return PosInf)
         ]

instance Arbitrary IntegerConstraint where
   arbitrary =
      oneof [
         validIntegerConstraint
         ]

validIntegerConstraint =
   do l <- frequency [(1,return NegInf), (2,liftM Val (choose (-2^10,2^10)))]
      u <- suchThat arbitrary (>= l)
      return (IntegerConstraint {lower = l, upper = u})

validConstraintAndInteger =
   do c <- validIntegerConstraint
      v <- suchThat arbitrary (liftM2 (&&) (>= (lower c)) (<= (upper c)))
      return (ConstraintAndInteger c v)

data ConstraintAndInteger = ConstraintAndInteger IntegerConstraint InfInteger
   deriving (Eq,Show)

instance Arbitrary ConstraintAndInteger where
   arbitrary = validConstraintAndInteger

prop_ValidConstraintAndInteger (ConstraintAndInteger c v) =
   v >= lower c && v <= upper c

\end{code}

\begin{code}

vInteger1 = Val 4096
tabInteger1 = myTAB'' (BT INTEGER) vInteger1

unConstrainedIntegerTest1 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 1" vInteger1 tabInteger1
   )

vInteger2 = Val 5002
tabInteger2 = myTAB'' (BT INTEGER) vInteger2

unConstrainedIntegerTest2 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 2" vInteger2 tabInteger2
   )

cInteger9 = UNION (IC (ATOM (E (V (R (4000,4254))))))
tInteger9 = ConsT (BT INTEGER) (RE cInteger9)
vInteger9'1 = Val 4002
tabInteger9'1 = myTAB'' tInteger9 vInteger9'1

constrainedIntegerTest1 =
   TestCase (
      assertEqual "Constrained INTEGER Test 1" vInteger9'1 tabInteger9'1
   )

tInteger9Extension = ConsT (BT INTEGER) (EXT cInteger9)
tabInteger9'1Extension = myTAB'' tInteger9Extension vInteger9'1

-- INTEGER (4000..4254)

constrainedIntegerExtensionTest1 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 1" vInteger9'1 tabInteger9'1Extension
   )

cInteger9'1 = UNION (IC (ATOM (E (V (R (5000,5254))))))
tInteger9Extension1 = ConsT (BT INTEGER) (EXTWITH cInteger9 cInteger9'1)
tabInteger9'1Extension1 = myTAB'' tInteger9Extension1 vInteger9'1

-- INTEGER (4000..4254, ..., 5000..5254)

constrainedIntegerExtensionTest2 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 2" vInteger9'1 tabInteger9'1Extension1
   )

vInteger9'2 = Val 5002
tabInteger9'1Extension2 = myTAB'' tInteger9Extension1 vInteger9'2

-- INTEGER (4000..4254, ..., 5000..5254)

constrainedIntegerExtensionTest3 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 3" vInteger9'2 tabInteger9'1Extension2
   )

tabSequence1 = myTAB'' tSequence1 vSequence1

sequenceTest1 =
   TestCase (
      assertEqual "SEQUENCE Test 1" vSequence1 tabSequence1
   )

tabSequence2 = myTAB'' tSequence2 vSequence1

sequenceTest2 =
   TestCase (
      assertEqual "SEQUENCE Test 2" vSequence1 tabSequence2
   )

vSequenceOf1 = take 3 $ repeat (BitString [1,1,1,1,1,1,1,1])
tabSequenceOf1 = myTAB'' incompleteSIBList vSequenceOf1

sequenceOfTest1 = 
   TestCase (
      assertEqual "SEQUENCE OF Test 1" vSequenceOf1 tabSequenceOf1
   )

vSequenceOf2 = take 127 $ repeat vInteger1
tabSequenceOf2 = myTAB'' (BT (SEQUENCEOF (BT INTEGER))) vSequenceOf2

sequenceOfTest2 =
   TestCase (
      assertEqual "SEQUENCE OF Test 2" vSequenceOf2 tabSequenceOf2
   )

tabSequenceOf3 = myTAB'' completeSIBList vSequenceOf1

sequenceOfTest3 = 
   TestCase (
      assertEqual "SEQUENCE OF Test 3" vSequenceOf1 tabSequenceOf3
   )

tests =
   [ unConstrainedIntegerTest1
   , unConstrainedIntegerTest2
   , constrainedIntegerTest1
   , constrainedIntegerExtensionTest1
   , constrainedIntegerExtensionTest2
   , constrainedIntegerExtensionTest3
   , sequenceTest1
   , sequenceTest2
   , sequenceOfTest1
   , sequenceOfTest2
   , sequenceOfTest3
   ]

main =
   do quickCheck prop_ValidConstraintAndInteger
      runTestTT (TestList tests)

\end{code}

\end{document}
