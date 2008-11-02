\section{Introduction}

Testing encoding for UNALIGNED PER

\begin{code}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -XFlexibleContexts
#-}

module TestCTR where

import CTRestruct
import Text.PrettyPrint
import NewPretty
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.Strict.BitPut as BP
import Control.Monad.Error

import qualified LatticeMod as L

import Test.QuickCheck
import Test.HUnit

import ASNTYPE
import ConstraintGeneration

import Language.ASN1(TagType(..), TagPlicity(..))

sc1 = UNION (UC (IC (ATOM (E (V (R (245,249)))))) (ATOM (E (V (R (251,255))))))
sc2 = UNION (IC (INTER (ATOM (E (V (R (270,273))))) (E (V (R (271,276))))))

con1 = RE (UNION (IC (ATOM (E (V (R (250,253)))))))
con2 = RE (UNION (IC (ATOM (E (V (R (245,253)))))))
con3 = RE sc1
con4 = EXT sc1
con5 = EXTWITH sc1 sc2

t1 = ConsT (BT INTEGER) con1
t2 = ConsT t1 con2
t3 = ConsT (ConsT (BT INTEGER) con2) con1
t4 = ConsT (BT INTEGER) con3
t5 = ConsT (BT INTEGER) con4
t6 = ConsT (BT INTEGER) con5
t7 = ConsT (ConsT (BT INTEGER) con5) con1

test1 = lEncode t1 252 []
test2 = lEncode t2 250 []
test3 = lEncode t3 250 []
test4 = lEncode t4 247 []
test5 = lEncode t5 247 []
test6 = lEncode t6 247 []
test7 = lEncode t6 272 []
test8 = lEncode t6 274 []
test9 = lEncode t7 251 []
test10 = lEncode t7 271 []
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

c1 = CTMandatory (NamedType "c1" (Just (Context,1,Explicit)) (BT INTEGER))
c2 = CTMandatory (NamedType "c2" (Just (Context,2,Explicit)) (BT INTEGER))

\end{code}

\begin{asn1}[caption={SEQUENCE Test 1},label=sequenceTest1]
SEQUENCE {c2 [2] EXPLICIT INTEGER,
          c1 [1] EXPLICIT INTEGER}
\end{asn1}

\begin{code}

tSequence1 = BT (SEQUENCE (Cons c2 (Cons c1 Nil)))
vSequence1 = (Val 3) :*: ((Val 5) :*: Empty)

myTest t x =
   case lEncode t x [] of
      Left s  -> s
      Right m -> show m -- (B.unpack (BP.runBitPut m))

{-
myTAB t x =
    case lEncode t x [] of
        Left s  -> error ("First " ++ s)
        Right y -> case decode2 t [] of
                     Left t -> error ("Second " ++ t)
                     Right x -> case BG.runBitGet (BP.runBitPut (bitPutify y)) (runErrorT x) of
                                   Left s -> error ("Third " ++ s)
                                   Right z -> case z of
                                                 Left u  -> error ("Fourth " ++ u)
                                                 Right n -> n
-}

myTAB' t x =
    case lEncode t x [] of
        Left s  -> error ("First " ++ s)
        Right y -> case decode2' t [] of
                     Left t -> error ("Second " ++ t)
                     Right x -> case BG.runBitGet (BP.runBitPut (bitPutify y)) (runErrorT x) of
                                   Left s -> error ("Third " ++ s)
                                   Right z -> case z of
                                                 Left u  -> error ("Fourth " ++ u)
                                                 Right n -> n

myTAB1 t x =
    case lEncode t x [] of
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
tabInteger1 = myTAB' (BT INTEGER) vInteger1

unConstrainedIntegerTest1 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 1" vInteger1 tabInteger1
   )

vInteger2 = Val 5002
tabInteger2 = myTAB' (BT INTEGER) vInteger2

unConstrainedIntegerTest2 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 2" vInteger2 tabInteger2
   )

cInteger9 = UNION (IC (ATOM (E (V (R (4000,4254))))))
tInteger9 = ConsT (BT INTEGER) (RE cInteger9)
vInteger9'1 = Val 4002
tabInteger9'1 = myTAB' tInteger9 vInteger9'1

constrainedIntegerTest1 =
   TestCase (
      assertEqual "Constrained INTEGER Test 1" vInteger9'1 tabInteger9'1
   )

tInteger9Extension = ConsT (BT INTEGER) (EXT cInteger9)
tabInteger9'1Extension = myTAB' tInteger9Extension vInteger9'1

-- INTEGER (4000..4254)

constrainedIntegerExtensionTest1 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 1" vInteger9'1 tabInteger9'1Extension
   )

cInteger9'1 = UNION (IC (ATOM (E (V (R (5000,5254))))))
tInteger9Extension1 = ConsT (BT INTEGER) (EXTWITH cInteger9 cInteger9'1)
tabInteger9'1Extension1 = myTAB' tInteger9Extension1 vInteger9'1

-- INTEGER (4000..4254, ..., 5000..5254)

constrainedIntegerExtensionTest2 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 2" vInteger9'1 tabInteger9'1Extension1
   )

vInteger9'2 = Val 5002
tabInteger9'1Extension2 = myTAB' tInteger9Extension1 vInteger9'2

-- INTEGER (4000..4254, ..., 5000..5254)

constrainedIntegerExtensionTest3 =
   TestCase (
      assertEqual "Constrained INTEGER Extension Test 3" vInteger9'2 tabInteger9'1Extension2
   )

tests =
   [ unConstrainedIntegerTest1
   , unConstrainedIntegerTest2
   , constrainedIntegerTest1
   , constrainedIntegerExtensionTest1
   , constrainedIntegerExtensionTest2
   , constrainedIntegerExtensionTest3
   ]

main =
   do quickCheck prop_ValidConstraintAndInteger
      runTestTT (TestList tests)

\end{code}

\end{document}
