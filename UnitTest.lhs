\documentclass{article}
%include polycode.fmt
\usepackage{listings}

\lstdefinelanguage{ASN1} {
  morekeywords={},
  sensitive=false,
  morecomment=[s]{(--}{--)}
  }

\begin{document}

\section{Introduction}

Note that some of the tests take a long time to run especially the one for encoding and decoding $256^{128}$.

\begin{code}

module UnitTest where

import ConstrainedType
import Pretty
import Control.Monad.State
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
import Data.Set hiding (map)
import Data.List hiding (groupBy)
import IO
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default), NamedType)
import qualified Data.Set as S
import Test.HUnit

\end{code}

\lstset{language=ASN1}
\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      T1 ::= INTEGER (25..30)
      Test1 ::=
         SEQUENCE {
            first  T1,
            second T1

      Test2 ::=
         SEQUENCE {
            first  T1 OPTIONAL,
            second T1 OPTIONAL
         }
   END
\end{lstlisting}

\begin{code}

t0 = INTEGER
t01 = INTEGER
t02 = INTEGER
t03 = INTEGER
t04 = INTEGER
t1' = RANGE INTEGER (Just 25) (Just 30)
t1 = CTMandatory (NamedType "" Nothing (RANGE INTEGER (Just 25) (Just 30)))
--t2 = INCLUDES INTEGER t1
--t3 = INCLUDES t1 t1
t4 = CTMandatory (NamedType "" Nothing (RANGE INTEGER (Just (-256)) Nothing))
t4' = CTOptional (NamedType "" Nothing (RANGE INTEGER (Just (-256)) Nothing))
t41 = RANGE INTEGER (Just 0) (Just 18000)
t42 = RANGE INTEGER (Just 3) (Just 3)
t5 = SEQUENCE (Cons t4 (Cons t4 Nil))
t6 = SEQUENCE (Cons t1 (Cons t1 Nil))
t7 = SIZE (SEQUENCEOF t1') (Elem (2,5)) NoMarker
t8 = SIZE (SEQUENCEOF t5) (Elem (2,2)) NoMarker
t9 = SEQUENCE (Cons t4' (Cons t4 Nil))
t10 = SIZE (SEQUENCEOF t9) (Elem (1,3)) NoMarker
t11 = CHOICE (ChoiceOption (NamedType "" Nothing t0)
         (ChoiceOption (NamedType "" Nothing t1')
         (ChoiceOption (NamedType "" Nothing t01)
         (ChoiceOption (NamedType "" Nothing t02) NoChoice))))
t12 = CHOICE (ChoiceOption (NamedType "" Nothing t04)
         (ChoiceOption (NamedType "" Nothing t03) NoChoice))

-- Constrained INTEGER

integer8'1 = toPer (RANGE INTEGER (Just 3) (Just 6)) 3
integer8'2 = toPer (RANGE INTEGER (Just 3) (Just 6)) 4
integer8'3 = toPer (RANGE INTEGER (Just 3) (Just 6)) 5
integer8'4 = toPer (RANGE INTEGER (Just 3) (Just 6)) 6
integer9'1 = toPer (RANGE INTEGER (Just 4000) (Just 4254)) 4002
integer9'2 = toPer (RANGE INTEGER (Just 4000) (Just 4254)) 4006
integer10'1 = toPer (RANGE INTEGER (Just 4000) (Just 4255)) 4002
integer10'2 = toPer (RANGE INTEGER (Just 4000) (Just 4255)) 4006
integer11'1 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 0
integer11'2 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 31000
integer11'3 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 32000
integer12'1 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 1
integer12'2 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 257
integer12'3 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 65538

integer13'1 = toPer (RANGE (RANGE INTEGER (Just 1) (Just 1)) (Just (-2)) Nothing) 1
integer13'2 = toPer (RANGE (RANGE INTEGER (Just 2) Nothing) (Just (-2)) (Just 3)) 3


test0 = toPer t1' 27

\end{code}

{-
test2 = toPer (SEQUENCE (Cons t1 (Cons t1 Nil))) (29:*:(30:*:Empty))
test2a = encodeSeqAux [] [] (Cons t1 (Cons t1 Nil)) (29:*:(30:*:Empty))
test20 = toPer (SEQUENCE (Cons t1 (Cons t1 (Cons t1 Nil)))) (29:*:(30:*:(26:*:Empty)))
test3 = toPer (SEQUENCE (Optional t1 (Optional t1 Nil))) ((Just 29):*:((Just 30):*:Empty))
test3a = encodeSeqAux [] [] (Optional t1 (Optional t1 Nil)) ((Just 29):*:((Just 30):*:Empty))
petest2 = toPer (SEQUENCE (Optional t1 (Optional t1 Nil)))

test4 = petest2 ((Just 29):*:((Just 30):*:Empty))
test5 = petest2 (Nothing:*:((Just 30):*:Empty))
test6 = petest2 ((Just 29):*:(Nothing:*:Empty))
test7 = petest2 (Nothing:*:(Nothing:*:Empty))
-}

\section{SEQUENCE OF}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      SeqOfElem1 ::= INTEGER (25..30)
      SeqOf ::=
         SEQUENCE OF SeqOfElem1
   END
\end{lstlisting}

\begin{code}

seqOfElem1 = RANGE INTEGER (Just 25) (Just 30)

seqOfType1 = SEQUENCEOF seqOfElem1

seqOfVal1 = [26,27,28,25]

test8 = toPer seqOfType1 seqOfVal1

eSeqOfElem1 = [
   0,0,0,0,0,1,0,0,
   0,0,1,
   0,1,0,
   0,1,1,
   0,0,0
   ]

eSeqOfTest1 =
   TestCase (
      assertEqual "SEQUENCE OF Test 1" eSeqOfElem1 test8
   )

dSeqOf1 = mmIdem seqOfType1 (toPer8s seqOfType1 seqOfVal1)

eSeqOfTest3 =
   TestCase (
      assertEqual "SEQUENCE OF Test 3" seqOfVal1 dSeqOf1
   )

seqOfVal1a = take 127 (cycle [25..30])

dSeqOf1a = mmIdem seqOfType1 (toPer8s seqOfType1 seqOfVal1a)

eSeqOfTest3a =
   TestCase (
      assertEqual "SEQUENCE OF Test 3a" seqOfVal1 dSeqOf1a
   )

eSeqOfTests3 n =
   TestCase (
      assertEqual ("SEQUENCE OF Test 3b" ++ show n) (seqOfVals3 n) (dSeqOfs3 n)
   )


seqOfVals3 n = genericTake n (cycle [25..30])

dSeqOfs3 n = mmIdem seqOfType1 (toPer8s seqOfType1 (seqOfVals3 n))

test9 = toPer (SEQUENCEOF t6) [29:*:(30:*:Empty),28:*:(28:*:Empty)]
test10
    = do
        c <- return (toPer (SEQUENCEOF t41) (take (17000) [1,2..]))
        writeFile "test12.txt" (show c)

test11
    = do
        c <- return (toPer (SEQUENCEOF t42) (take (17000) [3..]))
        writeFile "test14.txt" (show c)

test12
    = do
        c <- return (toPer (SEQUENCEOF t42) (take (93000) [3..]))
        writeFile "test15.txt" (show c)

\end{code}

\subsubsection{SIZE-CONSTRAINED SEQUENCEOF}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      SeqOf2 ::=
         SEQUENCE (SIZE (2..5)) OF SeqOfElem1
      SeqOf3 ::=
         SEQUENCE (SIZE (4..4)) OF SeqOfElem1
   END
\end{lstlisting}

\begin{code}

seqOft7 = SIZE (SEQUENCEOF seqOfElem1) (Elem (2,5)) NoMarker

seqOfType3 = SIZE (SEQUENCEOF seqOfElem1) (Elem (4,4)) NoMarker

seqOfVal7 = [26,25,28,27]

test14 = toPer seqOft7 seqOfVal7

eTest14 = [
   1,0,
   0,0,1,
   0,0,0,
   0,1,1,
   0,1,0
   ]

eSeqOfTest2 =
   TestCase (
      assertEqual "SEQUENCE OF Test 2" eTest14 test14
   )

dSeqOf7 = mmIdem seqOft7 (toPer8s seqOft7 seqOfVal7)

dSeqOf3 = mmIdem seqOfType3 (toPer8s seqOfType3 seqOfVal7)

eSeqOfTest4 =
   TestCase (
      assertEqual "SEQUENCE OF Test 4" seqOfVal7 dSeqOf7
   )

eSeqOfTest5 =
   TestCase (
      assertEqual "SEQUENCE OF Test 5" seqOfVal7 dSeqOf3
   )

\end{code}

\subsection{Dubuisson page 439}

\begin{quote}

A frame of 147,457 units is therefore fragmented
as follows:

11000100 65,536 units 11000100 65,536 units 11000001 16,384 units 00000001 1 unit

\end{quote}

\begin{code}

dub439e1 =
   TestCase (
      assertEqual
         "Dubuisson page 439 Example 1"
         [
            [1,1,0,0,0,1,0,0],
            [1,1,0,0,0,1,0,0],
            [1,1,0,0,0,0,0,1],
            [0,0,0,0,0,0,0,1]
         ]
         [
            take 8 x,
            take 8 y,
            take 8 z,
            take 8 a
         ]
   )
   where
      x = toPer seqOfType1 (seqOfVals3 147457)
      y = drop (3*64*(2^10)) (drop 8 x)
      z = drop (3*64*(2^10)) (drop 8 y)
      a = drop (3*16*(2^10)) (drop 8 z)

\end{code}

{-

*UnitTest> take 8 $ drop (3*64*(2^10)) $ drop 8 $ toPer seqOfType1 (seqOfVals3 147457)
[1,1,0,0,0,1,0,0]

*UnitTest> take 8 $ drop (3*64*(2^10)) $ drop 8 $ drop (3*64*(2^10)) $ drop 8 $ toPer
seqOfType1 (seqOfVals3 147457)
[1,1,0,0,0,0,1,0]
^^^^^^^^^^^^^^^^^ Does not match.

*UnitTest> take 8 $ drop (3*16*(2^10)) $ drop 8 $ drop (3*64*(2^10)) $ drop 8 $ drop
(3*64*(2^10)) $ drop 8 $ toPer seqOfType1 (seqOfVals3 147457)
[0,0,0,0,0,0,0,1]

-}

\subsection{Larmouth}


\begin{code}

larSeqOfT1 = SIZE (SEQUENCEOF seqOfElem1) (Elem (6,6)) NoMarker

larSeqOf1 = [0,0,0,0,0,1,0,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,0,0]

dLarSeqOf1 = mmIdem larSeqOfT1 larSeqOf1

lar303e1 =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 1"
         [25,26,27,28,29,30]
         dLarSeqOf1
   )

larSeqOfT2 = SIZE (SEQUENCEOF seqOfElem1) (Elem (5,20)) NoMarker

larSeqOf2 = [0,0,0,1,0,0,0,0,0,1,0,1,0,0,1,1,1,0,0,1,0,1,0,0]

dLarSeqOf2 = mmIdem larSeqOfT2 larSeqOf2

lar303e2 =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 2"
         [25,26,27,28,29,30]
         dLarSeqOf2
   )

larSeqOfT3 = SIZE (SEQUENCEOF seqOfElem1) (Elem (0,7)) NoMarker

larSeqOf3 = [0,1,1,0,0,0,0,0,1,0,1,0,0,0,0,0]

dLarSeqOf3 = mmIdem larSeqOfT3 larSeqOf3

lar303e3 =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 3"
         [25,26,27]
         dLarSeqOf3
   )

larSeqOfT4 = SEQUENCEOF seqOfElem1

larSeqOf4 = [0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,0,1]

dLarSeqOf4 = mmIdem larSeqOfT4 larSeqOf4

lar303e4 =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 4"
         [25,26,27,28,29,30,25,26]
         dLarSeqOf4
   )

larSeqOfT6 = SIZE (SEQUENCEOF seqOfElem1) (Elem (65534,65535)) NoMarker

larSeqOf6 = (0:(genericTake (65534*3) (cycle [0,0,0,0,0,1,0,1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,0,1]))) ++ [0,0,0,0,0]

dLarSeqOf6 = mmIdem larSeqOfT6 larSeqOf6

lar303e6 =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 6"
         (genericTake 65534 (cycle [25,26,27,28,29,30,25,26]))
         dLarSeqOf6
   )

larSeqOfT7 = SIZE (SEQUENCEOF seqOfElem1) (Elem (65537,65537)) NoMarker

larSeqOf7 =
   [1,1,0,0,0,1,0,0] ++ firstBlock ++ [0,0,0,0,0,0,0,1] ++ secondBlock ++ [0,0,0,0,0]
   where
      infContent  = cycle [0,0,0,0,0,1,0,1,0,0,1,1,1,0,0,1,0,1]
      firstBlock  = genericTake l infContent
      secondBlock = take 3 (genericDrop l infContent)
      l           = 65536*3

dLarSeqOf7 = mmIdem larSeqOfT7 larSeqOf7

lar303e7a =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 7a"
         eSample1
         aSample1
   )
   where
      eSample1 = take 6 expected
      aSample1 = take 6 actual
      expected = genericTake 65537 (cycle [25,26,27,28,29,30])
      actual   = dLarSeqOf7

lar303e7b =
   TestCase (
      assertEqual
         "Larmouth page 303 Example 7b"
         eSample2
         aSample2
   )
   where
      eSample2 = take 7 (genericDrop 65530 expected)
      aSample2 = take 7 (genericDrop 65530 actual)
      expected = genericTake 65537 (cycle [25,26,27,28,29,30])
      actual   = dLarSeqOf7

test15 = toPer t8 [(29:*:(30:*:Empty)),((-10):*:(2:*:Empty))]

test16 = toPer t10 [(Just (-10):*:(2:*:Empty))]

-- SET tests

test17
    = toPer (SET
              (Cons (CTMandatory (NamedType "" Nothing t1'))
                (Cons (CTMandatory (NamedType "" Nothing t0)) Nil)))
            (27 :*: (5 :*: Empty))

\end{code}

{-
test17a = toPer (SEQUENCE (Cons t1 (Cons t0 Nil))) (27 :*: (5 :*: Empty))
test17b = encodeSeqAux [] [] (Cons t1 (Cons t0 Nil)) (27 :*: (5 :*: Empty))

test18  = toPer (SET (Optional t1 (Optional t0 Nil))) ((Just 29):*:(Nothing:*:Empty))
test18a = toPer (SEQUENCE (Optional t1 (Optional t0 Nil))) ((Just 29):*:(Nothing:*:Empty))
test18b = encodeSeqAux [] [] (Optional t1 (Optional t0 Nil)) ((Just 29):*:(Nothing:*:Empty))

test19 = toPer (SET (Optional t1 (Optional t0 (Optional t01 Nil))))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))
test19a = toPer (SEQUENCE (Optional t1 (Optional t0 (Optional t01 Nil))))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))
test19b = encodeSeqAux [] [] (Optional t1 (Optional t0 (Optional t01 Nil)))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))
-}

\begin{code}

-- VISIBLESTRING tests

testvs1 = toPer VISIBLESTRING (VisibleString "Director")

-- VISIBLESTRING with permitted alphabet constraint and size constraints tests

x = (SIZE (FROM VISIBLESTRING (VisibleString ['0'..'9'])) (Elem (8,9)) NoMarker)

testvsc1 = toPer x (VisibleString "19710917")

-- X691: A.2.1 Example

prTest = toPer personnelRecord pr

pr = (emp :*: (t :*: (num :*: (hiredate :*: (sp :*: (Just cs :*: Empty))))))


personnelRecord
    = TYPEASS "PersonnelRecord" (Just (Application, 0, Implicit))
       (SET
         (Cons (CTMandatory (NamedType "name" Nothing name))
           (Cons (CTMandatory (NamedType "title" (Just (Context, 0, Explicit)) VISIBLESTRING))
             (Cons (CTMandatory (NamedType "number" Nothing empNumber))
               (Cons (CTMandatory (NamedType "dateOfHire" (Just (Context, 1, Explicit)) date))
                 (Cons (CTMandatory (NamedType "nameOfSpouse" (Just (Context, 2, Explicit)) name))
                   (Cons (CTDefault (NamedType "children" (Just (Context, 3,Implicit))
                                                             (SEQUENCEOF childInfo)) []) Nil)))))))

name
    = TYPEASS "Name" (Just (Application, 1, Implicit))
        (SEQUENCE
          (Cons (CTMandatory (NamedType "givenName" Nothing nameString))
            (Cons (CTMandatory (NamedType "initial" Nothing (SIZE nameString (Elem (1,1)) NoMarker)))
              (Cons (CTMandatory (NamedType "familyName" Nothing nameString)) Nil))))


t = VisibleString "Director"

empNumber
    = TYPEASS "EmployeeNumber" (Just (Application, 2, Implicit)) INTEGER

num = 51

date
    = TYPEASS "Date" (Just (Application, 3, Implicit))
        (SIZE (FROM VISIBLESTRING  (VisibleString ['0'..'9'])) (Elem (8,9)) NoMarker)

hiredate = VisibleString "19710917"


spGN = VisibleString "Mary"

spI  = VisibleString "T"

spFN = VisibleString "Smith"

sp = (spGN :*: (spI :*: (spFN :*: Empty)))

c1GN = VisibleString "Ralph"
c1I  = VisibleString "T"
c1FN = VisibleString "Smith"
c1BD = VisibleString "19571111"

c2GN = VisibleString "Susan"
c2I  = VisibleString "B"
c2FN = VisibleString "Jones"
c2BD = VisibleString "19590717"

c1 = ((c1GN :*: (c1I :*: (c1FN :*: Empty))) :*: (c1BD :*: Empty))
c2 = ((c2GN :*: (c2I :*: (c2FN :*: Empty))) :*: (c2BD :*: Empty))

cs = [c1,c2]


childInfo
    = TYPEASS "ChildInformation" Nothing
        (SET
            (Cons (CTMandatory (NamedType "name" Nothing name))
                (Cons (CTMandatory (NamedType "dateOfBirth" (Just (Context, 0, Explicit)) date)) Nil)))



nameString
    = TYPEASS "NameString" Nothing
        (SIZE (FROM VISIBLESTRING (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])) )
                            (Elem (1,64)) NoMarker)

empGN = VisibleString "John"

empFN = VisibleString "Smith"

empI = VisibleString "P"

emp = (empGN :*: (empI :*: (empFN :*: Empty)))


-- Another test (including multiple range constraint)

seqType
    = TYPEASS "seqType" Nothing
        (SEQUENCE
            (Cons (CTMandatory (NamedType "e" Nothing
                (SEQUENCE
                    (Cons (CTMandatory (NamedType "x" Nothing
                            (RANGE (RANGE INTEGER (Just 2) Nothing) (Just (-2)) (Just 3))))
                        (Cons (CTMandatory (NamedType "o" Nothing INTEGER)) Nil)))))
                (Cons (CTMandatory (NamedType "b" Nothing INTEGER))
                  (Cons (CTMandatory (NamedType "a" Nothing INTEGER)) Nil))))

seqVal
    = ((3 :*:
        (3 :*:Empty)):*:
            ((-1):*:
                (0:*:Empty)))

seqTest = toPer seqType seqVal

\end{code}


\section{Unconstrained INTEGER}

\begin{code}

tUnConInteger1 = INTEGER
vInteger1 = 4096
longIntegerVal1 = 256^4
longIntegerVal2 = 256^128

integer1 = toPer INTEGER 4096

mUn1 = mDecodeEncode tUnConInteger1 integer1

unConIntegerTest1 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 1" vInteger1 mUn1
   )

longInteger1 = toPer tUnConInteger1 longIntegerVal1
mUnLong1 = mDecodeEncode tUnConInteger1 longInteger1

unConIntegerTest2 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 2" longIntegerVal1 mUnLong1
   )

longInteger2 = toPer tUnConInteger1 longIntegerVal2
mUnLong2 = mDecodeEncode tUnConInteger1 longInteger2

unConIntegerTest3 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 3" longIntegerVal2 mUnLong2
   )

longInteger3 = toPer tUnConInteger1 longIntegerVal3
mUnLong3 = mDecodeEncode tUnConInteger1 longInteger3

unConIntegerTest4 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 4" longIntegerVal3 mUnLong3
   )

tUnConInteger2 = RANGE INTEGER Nothing (Just 65535)
vUnConInteger2 = 127
unConInteger2 = toPer tUnConInteger2 vUnConInteger2
mUn2 = mDecodeEncode tUnConInteger2 unConInteger2

integerTest2 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 5" vUnConInteger2 mUn2
   )

vUnConInteger3 = (-128)
unConInteger3 = toPer tUnConInteger2 vUnConInteger3
mUn3 = mDecodeEncode tUnConInteger2 unConInteger3

integerTest3 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 6" vUnConInteger3 mUn3
   )

vUnConInteger4 = 128
unConInteger4 = toPer tUnConInteger2 vUnConInteger4
mUn4 = mDecodeEncode tUnConInteger2 unConInteger4

integerTest4 =
   TestCase (
      assertEqual "Unconstrained INTEGER Test 7" vUnConInteger4 mUn4
   )

\end{code}

\section{Semi-Constrained INTEGER}

\begin{code}

tInteger5 = RANGE INTEGER (Just (-1)) Nothing
vInteger5 = 4096
integer5  = toPer (RANGE INTEGER (Just (-1)) Nothing) 4096

eInteger5 = [
   0,0,0,0,0,0,1,0,
   0,0,0,1,0,0,0,0,
   0,0,0,0,0,0,0,1
   ]

semiIntegerTest5 =
   TestCase (
      assertEqual "Semi-Constrained INTEGER Test 1" eInteger5 integer5
   )

tInteger6 = RANGE INTEGER (Just 1) Nothing
vInteger6 = 127
integer6  = toPer (RANGE INTEGER (Just 1) Nothing) 127
tInteger7 = RANGE INTEGER (Just 0) Nothing
vInteger7 = 128
integer7  = toPer (RANGE INTEGER (Just 0) Nothing) 128

mUnSemi5 = mDecodeEncode tInteger5 integer5
mSemiTest5 = vInteger5 == mUnSemi5

mUnSemi6 = mDecodeEncode tInteger6 integer6
mSemiTest6 = vInteger6 == mUnSemi6

mUnSemi7 = mDecodeEncode tInteger7 integer7
mSemiTest7 = vInteger7 == mUnSemi7

natural = RANGE INTEGER (Just 0) Nothing

longIntegerVal3 = 256^(2^11)
longIntegerPER3 = toPer natural longIntegerVal3
mSemiUnLong3 = mDecodeEncode natural longIntegerPER3
mUnLongTest3 = longIntegerVal3 == mSemiUnLong3

\end{code}


\section{BIT STRING}

\begin{code}

tBitString1 = BITSTRING []
vBitString1 = BitString [1,1,0,0,0,1,0,0,0,0]
bitString1  = toPer tBitString1 vBitString1

eBitString1 = [
   0,0,0,0,1,0,1,0,
   1,1,0,0,0,1,0,0,
   0,0
   ]

bitStringTest1 =
   TestCase (
      assertEqual "BIT STRING Test 1" eBitString1 bitString1
   )

dBitString1 = mmIdem tBitString1 (toPer8s tBitString1 vBitString1)

bitStringTest1a =
   TestCase (
      assertEqual "BIT STRING Test 1a" dBitString1 vBitString1
   )

vBitString1' = BitString [1,1]
bitString1'  = toPer tBitString1 vBitString1'

eBitString1' = [
   0,0,0,0,0,0,1,0,
   1,1
   ]

bitStringTest1' =
   TestCase (
      assertEqual "BIT STRING Test 2" eBitString1' bitString1'
   )

dBitString1' = mmIdem tBitString1 (toPer8s tBitString1 vBitString1')

bitStringTest1a' =
   TestCase (
      assertEqual "BIT STRING Test 2a" dBitString1' vBitString1'
   )

vBitString1'' = BitString [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
bitString1''  = toPer tBitString1 vBitString1''

eBitString1'' = [
   0,0,0,1,0,0,0,0,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1
   ]

bitStringTest1'' =
   TestCase (
      assertEqual "BIT STRING Test 3" eBitString1'' bitString1''
   )

dBitString1'' = mmIdem tBitString1 (toPer8s tBitString1 vBitString1'')

bitStringTest1a'' =
   TestCase (
      assertEqual "BIT STRING Test 3a" dBitString1'' vBitString1''
   )

\end{code}

\subsection{Size Constrained BIT STRING}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      BitString1 ::= BIT STRING (SIZE (7))
      BitString2 ::= BIT STRING (SIZE (12..15))
      BitString3 ::= BIT STRING (SIZE (0..2128))
      BitString4 ::= BIT STRING (SIZE (4..12,...,15))
   END
\end{lstlisting}

\begin{code}

tSConBitString1 = SIZE (BITSTRING []) (Elem (7,7)) NoMarker
vSConBitString1 = BitString [1,1,0,0,0,1,0]
sConBitString1  = toPer tSConBitString1 vSConBitString1

eSConBitString1 = [
   1,1,0,0,0,1,0
   ]

sConBitStringTest1 =
   TestCase (
      assertEqual "BIT STRING Test 4" eSConBitString1 sConBitString1
   )

dSConBitString1 = mmIdem tSConBitString1 (toPer8s tSConBitString1 vSConBitString1)

sConBitStringTest1a =
   TestCase (
      assertEqual "BIT STRING Test 4a" dSConBitString1 vSConBitString1
   )

tSConBitString2 = SIZE (BITSTRING []) (Elem (12,15)) NoMarker
vSConBitString2 = BitString [1,0,0,1,1,0,0,1,1,0,0,1,1]
sConBitString2  = toPer tSConBitString2 vSConBitString2

eSConBitString2 = [
   0,1,
   1,0,0,1,1,0,0,1,
   1,0,0,1,1
   ]

sConBitStringTest2 =
   TestCase (
      assertEqual "BIT STRING Test 5" eSConBitString2 sConBitString2
   )

dSConBitString2 = mmIdem tSConBitString2 (toPer8s tSConBitString2 vSConBitString2)

sConBitStringTest2a =
   TestCase (
      assertEqual "BIT STRING Test 5a" dSConBitString2 vSConBitString2
   )

tSConBitString3 = SIZE (BITSTRING []) (Elem (0,2128)) NoMarker
vSConBitString3 = BitString [1,1]
sConBitString3  = toPer tSConBitString3 vSConBitString3

eSConBitString3 = [
   0,0,0,0,0,0,0,0,
   0,0,1,0,
   1,1
   ]

sConBitStringTest3 =
   TestCase (
      assertEqual "BIT STRING Test 6" eSConBitString3 sConBitString3
   )

dSConBitString3 = mmIdem tSConBitString3 (toPer8s tSConBitString3 vSConBitString3)

sConBitStringTest3a =
   TestCase (
      assertEqual "BIT STRING Test 6a" dSConBitString2 vSConBitString2
   )

tSConBitString4 =
   SIZE (BITSTRING [])
        (Elem (4,12))
        (EM (Just (Elem (15,15))))
vSConBitString4 = BitString [1,1,0,0,0,1,0,0,0,0]
sConBitString4  = toPer tSConBitString4 vSConBitString4

eSConBitString4 = [
   0,
   0,1,1,0,
   1,1,0,0,0,1,0,0,
   0,0
   ]

sConBitStringTest4 =
   TestCase (
      assertEqual "BIT STRING Test 7" eSConBitString4 sConBitString4
   )

vSConBitString5 = BitString [1,1,0,0,0,1,0,0,0,0,1,0,1]
sConBitString5  = toPer tSConBitString4 vSConBitString5

eSConBitString5 = [
   1,
   1,0,0,1,
   1,1,0,0,0,1,0,0,
   0,0,1,0,1
   ]

sConBitStringTest5 =
   TestCase (
      assertEqual "BIT STRING Test 8" eSConBitString5 sConBitString5
   )

\end{code}

\section{ENUMERATED}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      Enum1 ::= ENUMERATED {
         red(-6), blue(20), green(-8)
         }
      Enum2 ::= ENUMERATED {
         red, blue, green, ..., yellow, purple
         }
      EnumeratedType1 ::= ENUMERATED {
         a, b(5), c, d(1), ..., e, f(6)
     }
      enum11 Enum1 ::= red
      enum12 Enum1 ::= blue
      enum13 Enum1 ::= green
      enum21 Enum2 ::= red
      enum22 Enum2 ::= yellow
      enum23 Enum2 ::= purple
   END
\end{lstlisting}

\begin{code}

testEnum = toPer et ev

et = ENUMERATED (EnumOption (Identifier "A")
                    (EnumOption (NamedNumber "B" 5)
                        (EnumOption (Identifier "C")
                            (EnumOption (NamedNumber "D" 1)
                                (EnumExt
                                    (EnumOption (Identifier "E")
                                        (EnumOption (NamedNumber "F" 6) NoEnum)))))))

ev = (Nothing :*:
        (Nothing :*:
            (Nothing :*:
                (Nothing :*:
                    (Nothing :*:
                        (Just "F" :*: Empty))))))

\end{code}

\section{CHOICE}

The example in X.691 section A.4.1 includes an extensible type with extension addition groups.

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      Choice1 ::=
        CHOICE {
          d INTEGER
    }

      Choice2 ::=
        CHOICE {
      a INTEGER,
          b INTEGER,
          c INTEGER,
          d INTEGER
        }

      SeqChoices1 ::=
         SEQUENCE {
            x Choice1,
            y Choice2
         }

      Ax ::=
         SEQUENCE {
            a    INTEGER (250..253),
            b    BOOLEAN,
            c    CHOICE {
                    d      INTEGER,
                    ...,
                    [[
                       e BOOLEAN,
                       f IA5String
                    ]],
                    ...
                 },
            ...,
            [[
               g NumericString (SIZE(3)),
               h BOOLEAN OPTIONAL
            ]],
            ...,
            i    BMPString OPTIONAL,
            j    PrintableString OPTIONAL
         }
   END
\end{lstlisting}

\begin{code}

choice1 =
   CHOICE xs
      where
         xs = ChoiceOption (NamedType "a" Nothing INTEGER) NoChoice

choiceVal1 = ValueC 7 EmptyHL

oldChoice1 =
   CHOICE xs
      where
         xs = ChoiceOption (NamedType "a" Nothing INTEGER) NoChoice

testOldChoice1 = toPer oldChoice1 (ValueC 31 EmptyHL)

eOldChoice1 = [
   0,0,0,0,0,0,0,1,
   0,0,0,1,1,1,1,1
   ]


choiceTest1 =
   TestCase (
      assertEqual "CHOICE Test 2" eOldChoice1 testOldChoice1
   )

xsChoice2 = xs
   where
      xs = ChoiceOption a (ChoiceOption b (ChoiceOption c (ChoiceOption d NoChoice)))
      a = NamedType "a" (Just (Context,5,Implicit)) INTEGER
      b = NamedType "b" (Just (Context,2,Implicit)) INTEGER
      c = NamedType "c" (Just (Context,7,Implicit)) INTEGER
      d = NamedType "d" (Just (Context,1,Implicit)) INTEGER

xsChoice3 = xs
   where
      xs = ChoiceOption a (ChoiceOption b (ChoiceOption c (ChoiceOption d NoChoice)))
      a  = NamedType "a" (Just (Context,5,Implicit)) INTEGER
      b  = NamedType "b" (Just (Context,7,Implicit)) ys
      c  = NamedType "c" (Just (Context,3,Implicit)) INTEGER
      d  = NamedType "d" (Just (Context,2,Implicit)) INTEGER
      ys = CHOICE (ChoiceOption e (ChoiceOption f (ChoiceOption g (ChoiceOption h NoChoice))))
      e = NamedType "e" (Just (Context,3,Implicit)) INTEGER
      f = NamedType "f" (Just (Context,13,Implicit)) INTEGER
      g = NamedType "g" (Just (Context,17,Implicit)) INTEGER
      h = NamedType "h" (Just (Context,19,Implicit)) INTEGER

xVal = NoValueC NoValue (ValueC      yVal (NoValueC NoValue (NoValueC NoValue EmptyHL)))
yVal = ValueC         7 (NoValueC NoValue (NoValueC NoValue (NoValueC NoValue EmptyHL)))

choice2 =
   CHOICE xs
      where
         xs = ChoiceOption a (ChoiceOption b (ChoiceOption c (ChoiceOption d NoChoice)))
         a = NamedType "a" Nothing INTEGER
         b = NamedType "b" Nothing INTEGER
         c = NamedType "c" Nothing INTEGER
         d = NamedType "d" Nothing INTEGER

choiceVal2 = NoValueC NoValue (NoValueC NoValue (NoValueC NoValue (ValueC 7 EmptyHL)))

oldChoice2 =
   CHOICE xs
      where
         xs = ChoiceOption a (ChoiceOption b (ChoiceOption c (ChoiceOption d NoChoice)))
         a = NamedType "a" Nothing INTEGER
         b = NamedType "b" Nothing INTEGER
         c = NamedType "c" Nothing INTEGER
         d = NamedType "d" Nothing INTEGER

testOldChoice2 = toPer oldChoice2 (NoValueC NoValue (ValueC 27 (NoValueC NoValue (NoValueC NoValue EmptyHL))))

eOldChoice2 = [
   0,1,
   0,0,0,0,0,0,0,1,
   0,0,0,1,1,0,1,1
   ]


choiceTest2 =
   TestCase (
      assertEqual "CHOICE Test 3" eOldChoice2 testOldChoice2
   )

testOldChoice21 = toPer oldChoice2 (ValueC 31 (NoValueC NoValue (NoValueC NoValue (NoValueC NoValue EmptyHL))))

eOldChoice21 = [
   0,0,
   0,0,0,0,0,0,0,1,
   0,0,0,1,1,1,1,1
   ]


choiceTest21 =
   TestCase (
      assertEqual "CHOICE Test 4" eOldChoice21 testOldChoice21
   )

decodeChoice1 = mmIdem choice1 eOldChoice1

choiceTest3 =
   TestCase (
      assertEqual "CHOICE Test 5" (show (ValueC 31 EmptyHL)) (show decodeChoice1)
   )

\end{code}

We have to pad to a multiple of 8 bits otherwise the tests don't work.
This really needs to be fixed.




\begin{code}

decodeChoice2 = mmIdem choice2 (eOldChoice21 ++ (take 6 (repeat 0)))

choiceTest4 =
   TestCase (
      assertEqual
         "CHOICE Test 6"
         (show (ValueC 31 (NoValueC (NoValue::Phantom Integer) (NoValueC (NoValue::Phantom Integer) (NoValueC (NoValue::Phantom Integer) EmptyHL)))))
         (show decodeChoice2)
   )

seqChoices1 =
   SEQUENCE elems
      where
         elems = Cons x (Cons y Nil)
         x = CTMandatory (NamedType "x" Nothing choice1)
         y = CTMandatory (NamedType "y" Nothing choice2)

\end{code}


\begin{code}

ax
    = TYPEASS "Ax" Nothing
        (SEQUENCE
            (Cons (CTMandatory (NamedType "a" Nothing (RANGE INTEGER (Just 250) (Just 253))))
                (Cons (CTMandatory (NamedType "b" Nothing BOOLEAN))
                  (Cons (CTMandatory (NamedType "c" Nothing
                         (CHOICE
                          (ChoiceOption (NamedType "d" Nothing INTEGER)
                            (ChoiceExt
                              (ChoiceEAG
                                (ChoiceOption (NamedType "e" Nothing BOOLEAN)
                                  (ChoiceOption (NamedType "f" Nothing IA5STRING)
                                     (ChoiceEAG
                                       (ChoiceExt NoChoice))))))))))
                    (Extens
                        (Cons (CTExtMand (NamedType "" Nothing
                               (EXTADDGROUP
                                (Cons (CTExtMand (NamedType "g" Nothing (SIZE NUMERICSTRING (Elem (3,3)) NoMarker)))
                                     (Cons (CTOptional (NamedType "h" Nothing BOOLEAN)) Nil)))))
                            (Extens
                                (Cons (CTOptional (NamedType "i" Nothing VISIBLESTRING))
                                  (Cons (CTOptional (NamedType "j" Nothing VISIBLESTRING)) Nil)))))))))


axVal
    = (253 :*:
       (True :*:
         ((NoValueC NoValue
            (ValueC True (NoValueC NoValue EmptyHL))) :*:
               ((Just (Just (NumericString "123") :*:(Just True :*: Empty))):*:
                 (Nothing :*:
                  (Nothing :*:Empty))))))

axEx = toPer ax axVal

eAx = [
   1,
   0,0,
   1,1,
   1,
   1,
   0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,1,
   1,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,
   1,
   0,0,0,0,0,0,1,0,
   1,
   0,0,1,0,0,0,1,1,0,1,0,0,
   1,0,0,0,0
   ]


sChoiceTest1 =
   TestCase (
      assertEqual "CHOICE Test 1" eAx axEx
   )

\end{code}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      Choice3 ::=
        CHOICE {
      a INTEGER,
          b BIT STRING,
        }
   END
\end{lstlisting}

\begin{code}

choice3 = TYPEASS "Choice3" Nothing (CHOICE cs)
   where
      cs = ChoiceOption a (ChoiceOption b NoChoice)
      a = NamedType "a" Nothing INTEGER
      b = NamedType "b" Nothing (BITSTRING [])

testChoice3 = toPer choice3 (ValueC 3 (NoValueC NoValue EmptyHL))

test20c  = toPer (CHOICE (ChoiceOption (NamedType "" Nothing t0)
                 (ChoiceOption (NamedType "" Nothing t1')
                   (ChoiceOption (NamedType "" Nothing t01)
                 (ChoiceOption (NamedType "" Nothing t02) NoChoice)))))
            (NoValueC NoValue (ValueC 27 (NoValueC NoValue (NoValueC NoValue EmptyHL))))

test21c  = toPer (CHOICE (ChoiceOption (NamedType "" Nothing t0) NoChoice)) (ValueC 31 EmptyHL)

test22c
  = toPer (CHOICE (ChoiceOption (NamedType "" Nothing t0)
            (ChoiceOption (NamedType "" Nothing t12) NoChoice)))
             (NoValueC NoValue (ValueC (ValueC 52 (NoValueC NoValue EmptyHL)) EmptyHL))

test23c
    = toPer (CHOICE (ChoiceOption (NamedType "" Nothing t11)
        (ChoiceOption (NamedType "" Nothing t12) NoChoice)))
        (ValueC (NoValueC NoValue (ValueC 27 (NoValueC NoValue (NoValueC NoValue EmptyHL))))
            (NoValueC NoValue EmptyHL))

\end{code}

Tests arising from QuickCheck property failures. It looks like the failure was caused
by the encoding not being a multiple of 8 bits. Wrong! They were caused by DJS' misunderstanding
of the bit mask for CHOICE. This test is updated to be valide ASN.1 in which tags
are used to disambiguate which alternative of the CHOICE is being encoded / decoded.

\begin{code}

quickFailType1 =
   CHOICE xs
      where
         xs = ChoiceOption p (ChoiceOption n NoChoice)
         p = NamedType "p" (Just (Context,0,Implicit)) INTEGER
         n = NamedType "n" (Just (Context,1,Implicit)) INTEGER

quickFailVal1 = NoValueC NoValue (ValueC   0       EmptyHL)
quickFailVal2 = ValueC   0       (NoValueC NoValue EmptyHL)

qF1 = mmIdem quickFailType1 (toPer8s quickFailType1 quickFailVal1)

qFTest1 =
   TestCase (
      assertEqual "CHOICE Test 7" quickFailVal1 qF1
   )

quickFailType2 =
   CHOICE xs
      where
         xs  = ChoiceOption x (ChoiceOption omu NoChoice)
         x   = NamedType "x" Nothing s
         omu = NamedType "omu" Nothing r1
         r1  = RANGE r2 (Just 3) (Just 3)
         r2  = RANGE r3 (Just 2) (Just 3)
         r3  = RANGE INTEGER (Just (-2)) (Just 7)
         s   = SEQUENCE (Cons (CTMandatory (NamedType "y" Nothing INTEGER)) Nil)

quickFailVal3 = ValueC ((-2) :*: Empty) (NoValueC NoValue EmptyHL)

qF2 = mmIdem quickFailType2 (toPer8s quickFailType2 quickFailVal3)

qFTest2 =
   TestCase (
      assertEqual "CHOICE Test 8" quickFailVal3 qF2
   )

quickFailType2a =
   CHOICE xs
      where
         xs  = ChoiceOption x (ChoiceOption zmu NoChoice)
         x   = NamedType "x" Nothing s
         zmu = NamedType "zmu" Nothing r1
         r1  = RANGE r2 (Just 3) (Just 3)
         r2  = RANGE r3 (Just 2) (Just 3)
         r3  = RANGE INTEGER (Just (-2)) (Just 7)
         s   = SEQUENCE (Cons (CTMandatory (NamedType "y" Nothing INTEGER)) Nil)

quickFailVal3a = ValueC ((-2) :*: Empty) (NoValueC NoValue EmptyHL)

qF2a = mmIdem quickFailType2a (toPer8s quickFailType2a quickFailVal3a)

qFTest2a =
   TestCase (
      assertEqual "CHOICE Test 8a" quickFailVal3a qF2a
   )

quickFailType10 =
   CHOICE
      (ChoiceOption
         (NamedType "yn" (Just (Context, 0, Implicit)) INTEGER)
         (ChoiceOption
            (NamedType "h" Nothing INTEGER)
            NoChoice
         )
      )

quickFailVal10 = NoValueC NoValue (ValueC (-2) EmptyHL)

qF10 = mmIdem quickFailType10 (toPer8s quickFailType10 quickFailVal10)

qFTest10 =
   TestCase (
      assertEqual "CHOICE Test 10" quickFailVal10 qF10
   )

{-
CHOICE {wa [0] IMPLICIT SEQUENCE {c [0] IMPLICIT INTEGER},
        a [0] IMPLICIT CHOICE {p INTEGER},
        j INTEGER}: wa:{c 0}
-}

quickFailType11 =
   CHOICE
      (ChoiceOption
         (NamedType "wa" (Just (Context, 0, Implicit)) seq11)
         (ChoiceOption
            (NamedType "a" (Just (Context, 2, Implicit)) choice11)
            (ChoiceOption
               (NamedType "j" Nothing INTEGER)
               NoChoice
            )
         )
      )
   where
      seq11 = SEQUENCE (Cons (CTMandatory (NamedType "c" (Just (Context, 1, Implicit)) INTEGER)) Nil)
      choice11 = CHOICE (ChoiceOption (NamedType "p" Nothing INTEGER) NoChoice)

quickFailVal11 =
   ValueC wa (NoValueC NoValue (NoValueC NoValue EmptyHL))
   where
      wa =  0 :*: Empty

qF11 = mmIdem quickFailType11 (toPer8s quickFailType11 quickFailVal11)

qFTest11 =
   TestCase (
      assertEqual "CHOICE Test 11" quickFailVal11 qF11
   )

\end{code}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      Choice9a ::=
         CHOICE {
            a CHOICE {
               b INTEGER,
               c SEQUENCE {}
               },
            d SEQUENCE {
               e INTEGER,
               f BIT STRING
               }
            }

      Choice9b ::=
         CHOICE {
            a CHOICE {
               b INTEGER,
               c BOOLEAN
               },
            d SEQUENCE {
               e INTEGER,
               f BIT STRING
               }
            }
   END
\end{lstlisting}

\begin{code}

xsChoice9 = xs
   where
      xs = ChoiceOption a (ChoiceOption d NoChoice)
      a  = NamedType "a" Nothing (CHOICE (ChoiceOption b (ChoiceOption c NoChoice)))
      b  = NamedType "b" Nothing INTEGER
      c  = NamedType "c" Nothing (SEQUENCE Nil)
      d  = NamedType "d" Nothing (SEQUENCE (Cons e (Cons f Nil)))
      e  = CTMandatory (NamedType "e" Nothing INTEGER)
      f  = CTMandatory (NamedType "f" Nothing (BITSTRING []))

xsChoiceVal91 = NoValueC NoValue (ValueC d EmptyHL)
   where
      d = 3 :*: ((BitString [1,1,1,0,1,1,0,1]) :*: Empty)

xsChoiceVal92 = ValueC a (NoValueC NoValue EmptyHL)
   where
      a = ValueC 9 (NoValueC NoValue EmptyHL)

xsChoiceVal93 = ValueC a (NoValueC NoValue EmptyHL)
   where
      a = NoValueC NoValue (ValueC Empty EmptyHL)

xsChoice9b = xs
   where
      xs = ChoiceOption a (ChoiceOption d NoChoice)
      a  = NamedType "a" Nothing (CHOICE (ChoiceOption b (ChoiceOption c NoChoice)))
      b  = NamedType "b" Nothing INTEGER
      c  = NamedType "c" Nothing BOOLEAN
      d  = NamedType "d" Nothing (SEQUENCE (Cons e (Cons f Nil)))
      e  = CTMandatory (NamedType "e" Nothing INTEGER)
      f  = CTMandatory (NamedType "f" Nothing (BITSTRING []))

xsChoiceVal9b1 = NoValueC NoValue (ValueC d EmptyHL)
   where
      d = 3 :*: ((BitString [1]) :*: Empty)

xsChoiceVal9b2 = ValueC a (NoValueC NoValue EmptyHL)
   where
      a = ValueC 9 (NoValueC NoValue EmptyHL)

xsChoiceVal9b3 = ValueC a (NoValueC NoValue EmptyHL)
   where
      a = NoValueC NoValue (ValueC True EmptyHL)

\end{code}

\section{SEQUENCE}

\begin{lstlisting}[frame=single]
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      Seq1 ::=
        SEQUENCE {
          SEQUENCE {
             INTEGER (25..30)
          }
    }
   END
\end{lstlisting}

\begin{code}

tSeq1 =
   SEQUENCE testSeq1
      where
         testSeq1 = Cons (CTMandatory (NamedType "" Nothing (SEQUENCE subSeq1))) Nil
         subSeq1  = Cons (CTMandatory (NamedType "" Nothing consInt1)) Nil
         consInt1 = RANGE INTEGER (Just 25) (Just 30)

vSeq1 = (27:*:Empty):*:Empty

sSeq1 = toPer tSeq1 vSeq1

eSeq1 = [
   0,1,0
   ]

sSeqTest1 =
   TestCase (
      assertEqual "SEQUENCE Test 1" eSeq1 sSeq1
   )

\end{code}

\section{Blah}

\begin{code}

mDecodeEncode :: ASNType Integer -> BitStream -> Integer
mDecodeEncode t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

\end{code}

{-
mIdem :: ASNType a -> BitStream -> a
mIdem t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest = runState . runErrorT . fromPer t . B.pack . map (fromIntegral . fromNonNeg) . groupBy 8
-}

\begin{code}

mmIdem :: ASNType a -> BitStream -> a
mmIdem t x =
   case runTest x 0 of
      (Left ys,s)   -> error (show ys ++ " " ++ show s)
      (Right xs,_) -> xs
   where
      runTest x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

testType3 = SEQUENCE (Cons (CTOptional (NamedType "l1" Nothing t1')) (Cons (CTOptional (NamedType "l1" Nothing t1')) Nil))
testVal3  = (Just 29):*:((Just 30):*:Empty)
testToPer3 = toPer testType3 testVal3
testFromPer3 = mmIdem testType3 testToPer3

testVal3'  = (Just 29):*:(Nothing:*:Empty)
testToPer3' = toPer testType3 testVal3'
-- Note that this gives the wrong answer as we don't yet pad the encoding to a multiple of 8 bits.
-- It's exposed because we use groupBy 8.
testFromPer3' = mmIdem testType3 testToPer3'

\end{code}

{-
testType2 = SEQUENCE (Cons t1 (Cons t1 Nil))
testVal2  = 29:*:(30:*:Empty)
testToPer2 = toPer testType2 testVal2
testFromPer2 = mIdem testType2 testToPer2

testType3 = SEQUENCE (Optional t1 (Optional t1 Nil))




seq1 = SEQUENCE (Cons t1 (Cons t1 Nil))

seqTest1 =
   case d of
      (Left x,(u,v))   -> show x
      (Right x,(u,v)) -> show x

d = runState (runErrorT (mFromPer seq1)) (B.pack [0xb4],0)

seq2 = SEQUENCE (Optional t1 (Optional t1 Nil))

seqTest :: Show a => ASNType a -> [Word8] -> String
seqTest t xs =
   case d of
      (Left x,(u,v))   -> show x
      (Right x,(u,v)) -> show x
   where d = runState (runErrorT (mFromPer t)) (B.pack xs,0)
-}

\begin{code}

type1 = NamedType "T1" Nothing (RANGE INTEGER (Just 25) (Just 30))

type2 = NamedType "T2" Nothing (SEQUENCE (Cons (CTMandatory (NamedType "first" Nothing INTEGER)) Nil))

type3 =
   NamedType "T3" Nothing (SEQUENCE (
      Cons (CTMandatory (NamedType "first" Nothing INTEGER)) (
         Cons (CTMandatory (NamedType "second" Nothing INTEGER)) Nil)))

type7       = NamedType "T3" Nothing (SEQUENCE (Cons (CTMandatory type7First) (Cons (CTMandatory type7Second) (Cons (CTMandatory type7Nest1) Nil))))
type7First  = NamedType "first" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Second = NamedType "second" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Fourth) (Cons (CTMandatory type7Nest2) Nil))))
type7Third  = NamedType "third" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Fourth = NamedType "fourth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Sixth) Nil)))
type7Fifth  = NamedType "fifth" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Sixth  = NamedType "sixth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

testType7 = let NamedType _ _ t = type7Nest1 in toPer t (7:*:(11:*:((13:*:(17:*:Empty)):*:Empty)))

testType7' = let NamedType _ _ t = type7 in toPer t (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty)))

thereAndBack7 =
   let NamedType _ _ t = type7 in
      mmIdem t (toPer t (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty))))

type8       = NamedType "T4" Nothing (SEQUENCE (Cons (CTMandatory type8First) (Cons (CTMandatory type8Second) (Cons (CTMandatory type8Nest1) Nil))))
type8First  = NamedType "first"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Second = NamedType "second" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

type8Nest1  = NamedType "nest1"  Nothing (SEQUENCE (Cons (CTMandatory type8Third) (Cons (CTMandatory type8Fourth) Nil)))
type8Third  = NamedType "third"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Fourth = NamedType "fourth" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

testType8 =
   let (NamedType _ _ t) = type8 in
      toPer t ((BitString [1,0,1,0,0,0,0,0]):*:((BitString [1,0,1,0,0,0,0,0]):*:(((BitString [1,0,1,0,0,0,0,0]):*:((BitString [1,0,1,0,0,0,0,0]):*:Empty)):*:Empty)))

thereAndBack8 =
   let NamedType _ _ t = type8 in
      mmIdem t (toPer t ((BitString [1,0,1,0,0,0,0,0]):*:((BitString [1,0,1,0,0,0,0,0]):*:(((BitString [1,0,1,0,0,0,0,0]):*:((BitString [1,0,1,0,0,0,0,0]):*:Empty)):*:Empty))))

bs8' n = take n (cycle [1,0,1,0,0,0,0,0])

type9       = NamedType "T5" Nothing (SEQUENCE (Cons (CTMandatory type9First) (Cons (CTMandatory type9Second) Nil)))
type9First  = NamedType "first"  Nothing (RANGE INTEGER (Just 0) (Just 65535))
type9Second = NamedType "second" Nothing (SIZE (BITSTRING []) (Elem (0,65544)) NoMarker)

val9 = 2:*:((BitString (bs8' 52)):*:Empty)

val91 = 2:*:((BitString (bs8' ((2^16) + 8))):*:Empty)

thereAndBack9 =
   let NamedType _ _ t = type9 in
      mmIdem t (toPer t val9)

thereAndBack91 =
   let NamedType _ _ t = type9 in
      mmIdem t (toPer t val91)

type10 = NamedType "T6" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

val10 = BitString (bs8' 56)

val101 = BitString (bs8' ((2^16) + 8))

thereAndBack10 =
   let NamedType _ _ t = type10 in
      mmIdem t (toPer t val10)

thereAndBack101 =
   let NamedType _ _ t = type10 in
      mmIdem t (toPer t val101)

type4 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (0,4)) NoMarker)

type5 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (0,14)) NoMarker)

type6 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (0,((2^16)+1))) NoMarker)

foo (NamedType _ _ t) =
   do h <- openFile "test" ReadMode
      b <- B.hGetContents h
      let d = runState (runErrorT (mFromPer t)) (b,0)
      case d of
         (Left e,s)  -> return (e ++ " " ++ show s)
         (Right n,s) -> return (show n ++ " " ++ show s)

tests =
   [
   unConIntegerTest1,
   unConIntegerTest2,
   unConIntegerTest3,
--    unConIntegerTest4, --
   integerTest2,
   integerTest3,
   integerTest4,
   semiIntegerTest5,
   bitStringTest1,
   bitStringTest1a,
   bitStringTest1',
   bitStringTest1a',
   bitStringTest1'',
   bitStringTest1a'',
   sConBitStringTest1,
   sConBitStringTest1a,
   sConBitStringTest2,
   sConBitStringTest2a,
   sConBitStringTest3,
   sConBitStringTest3a,
   sConBitStringTest4,
   sConBitStringTest5,
   choiceTest1,
   choiceTest2,
   choiceTest21,
   choiceTest3,
   choiceTest4,
   qFTest1,
   qFTest2,
   qFTest2a,
   qFTest10,
   qFTest11,
   sChoiceTest1,
   eSeqOfTest1,
   eSeqOfTest2,
   eSeqOfTest3,
   eSeqOfTest4,
   eSeqOfTest5,
   sSeqTest1,
--    dub439e1, --
   lar303e1,
   lar303e2,
   lar303e3,
   lar303e4 --,
--    lar303e6, --
--    lar303e7a, --
--    lar303e7b --
   ]


main = runTestTT (TestList (tests ++ (map eSeqOfTests3 [127,128,129])))

\end{code}

\end{document}
