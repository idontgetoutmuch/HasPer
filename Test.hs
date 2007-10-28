import ConstrainedType
import Control.Monad.State
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
import Data.Set hiding (map)
import IO
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default), NamedType)
import qualified Data.Set as S

{-
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
-}


t0 = INTEGER
t01 = INTEGER
t02 = INTEGER
t03 = INTEGER
t04 = INTEGER
t1' = RANGE INTEGER (Just 25) (Just 30)
t1 = ETMandatory (NamedType "" Nothing (RANGE INTEGER (Just 25) (Just 30)))
--t2 = INCLUDES INTEGER t1
--t3 = INCLUDES t1 t1
t4 = ETMandatory (NamedType "" Nothing (RANGE INTEGER (Just (-256)) Nothing))
t4' = ETOptional (NamedType "" Nothing (RANGE INTEGER (Just (-256)) Nothing))
t41 = RANGE INTEGER (Just 0) (Just 18000)
t42 = RANGE INTEGER (Just 3) (Just 3)
t5 = SEQUENCE (Cons t4 (Cons t4 Nil))
t6 = SEQUENCE (Cons t1 (Cons t1 Nil))
t7 = SIZE (SEQUENCEOF t1') (Elem (fromList [2..5])) NoMarker
t8 = SIZE (SEQUENCEOF t5) (Elem (fromList [2])) NoMarker
t9 = SEQUENCE (Cons t4' (Cons t4 Nil))
t10 = SIZE (SEQUENCEOF t9) (Elem (fromList [1..3])) NoMarker
--t11 = CHOICE (ChoiceOption t0 (ChoiceOption t1 (ChoiceOption t01 (ChoiceOption t02 NoChoice))))
--t12 = CHOICE (ChoiceOption t04 (ChoiceOption t03 NoChoice))

-- Unconstrained INTEGER
tInteger1 = INTEGER
vInteger1 = 4096
integer1 = toPer INTEGER 4096
integer2 = toPer (RANGE INTEGER Nothing (Just 65535)) 127
tInteger2 = RANGE INTEGER Nothing (Just 65535)
vInteger2 = 127
integer3 = toPer (RANGE INTEGER Nothing (Just 65535)) (-128)
integer4 = toPer (RANGE INTEGER Nothing (Just 65535)) 128


-- Semi-constrained INTEGER

tInteger5 = RANGE INTEGER (Just (-1)) Nothing
vInteger5 = 4096
integer5  = toPer (RANGE INTEGER (Just (-1)) Nothing) 4096
tInteger6 = RANGE INTEGER (Just 1) Nothing
vInteger6 = 127
integer6  = toPer (RANGE INTEGER (Just 1) Nothing) 127
tInteger7 = RANGE INTEGER (Just 0) Nothing
vInteger7 = 128
integer7  = toPer (RANGE INTEGER (Just 0) Nothing) 128


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

-- ENUMERATED TYPE

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
-- BitString

bsTest1  = toPer (BITSTRING []) (BitString [1,1,0,0,0,1,0,0,0,0])
bsTest1' = toPer (BITSTRING []) (BitString [1,1])
bsTest1'' = toPer (BITSTRING []) (BitString [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])

-- Size-constrained (BITSTRING [])

bsTest2 = toPer (SIZE (BITSTRING []) (Elem (fromList [7])) NoMarker) (BitString [1,1,0,0,0,1,0,0,0,0])
bsTest3 = toPer (SIZE (BITSTRING []) (Elem (fromList [12..15])) NoMarker)(BitString [1,1,0,0,0,1,0,0,0,0])
bsTest3' = toPer (SIZE (BITSTRING []) (Elem (fromList [0..2128])) NoMarker) (BitString [1,1])


-- Extensible Size-Constrained (BITSTRING [])

bsTest4 = toPer (SIZE (BITSTRING []) (Elem (fromList [4..12])) (EM (Just (Elem (fromList [15])))))
                (BitString [1,1,0,0,0,1,0,0,0,0])
bsTest4' = toPer (SIZE (BITSTRING []) (Elem (fromList [4..12])) (EM (Just (Elem (fromList [15])))))
                (BitString [1,1,0,0,0,1,0,0,0,0,1,0,1])
-- SEQUENCE

test1 = toPer (SEQUENCE (Cons (ETMandatory (NamedType "" Nothing
                (SEQUENCE (Cons (ETMandatory (NamedType "" Nothing t1'))
            Nil)))) Nil)) ((27:*:Empty):*:Empty)
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
-- SEQUENCEOF
test8 = toPer (SEQUENCEOF t1') [26,27,28,25]
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

-- SIZE-CONSTRAINED SEQUENCEOF

test14 = toPer t7 [26,25,28,27]

test15 = toPer t8 [(29:*:(30:*:Empty)),((-10):*:(2:*:Empty))]

test16 = toPer t10 [(Just (-10):*:(2:*:Empty))]

-- SET tests

test17
    = toPer (SET
              (Cons (ETMandatory (NamedType "" Nothing t1'))
                (Cons (ETMandatory (NamedType "" Nothing t0)) Nil)))
            (27 :*: (5 :*: Empty))

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
-- CHOICE tests
{-
test20c  = toPer (CHOICE (ChoiceOption t0 (ChoiceOption t1 (ChoiceOption t01 (ChoiceOption t02 NoChoice)))))
            (Nothing :*: (Just 27 :*: (Nothing :*: (Nothing :*: Empty))))

test21c  = toPer (CHOICE (ChoiceOption t0 NoChoice)) (Just 31 :*: Empty)

test22c
  = toPer (CHOICE (ChoiceOption t0 (ChoiceOption t12 NoChoice)))
             (Nothing :*: (Just (Just 52 :*: (Nothing :*: Empty)) :*: Empty))

test23c
    = toPer (CHOICE (ChoiceOption t11 (ChoiceOption t12 NoChoice)))
        (Just (Nothing :*: (Just 27 :*: (Nothing :*: (Nothing :*: Empty))))
            :*: (Nothing :*: Empty))
-}
-- VISIBLESTRING tests

testvs1 = toPer VISIBLESTRING (VisibleString "Director")

-- VISIBLESTRING with permitted alphabet constraint and size constraints tests

x = (SIZE (FROM VISIBLESTRING (VisibleString ['0'..'9'])) (Elem (fromList [8,9])) NoMarker)

testvsc1 = toPer x (VisibleString "19710917")

-- X691: A.2.1 Example

prTest = toPer personnelRecord pr

pr = (emp :*: (t :*: (num :*: (hiredate :*: (sp :*: (Just cs :*: Empty))))))


personnelRecord
    = TYPEASS "PersonnelRecord" (Just (Application, 0, Implicit))
       (SET
         (Cons (ETMandatory (NamedType "name" Nothing name))
           (Cons (ETMandatory (NamedType "title" (Just (Context, 0, Explicit)) VISIBLESTRING))
             (Cons (ETMandatory (NamedType "number" Nothing empNumber))
               (Cons (ETMandatory (NamedType "dateOfHire" (Just (Context, 1, Explicit)) date))
                 (Cons (ETMandatory (NamedType "nameOfSpouse" (Just (Context, 2, Explicit)) name))
                   (Cons (ETDefault (NamedType "children" (Just (Context, 3,Implicit))
                                                             (SEQUENCEOF childInfo)) []) Nil)))))))

name
    = TYPEASS "Name" (Just (Application, 1, Implicit))
        (SEQUENCE
          (Cons (ETMandatory (NamedType "givenName" Nothing nameString))
            (Cons (ETMandatory (NamedType "initial" Nothing (SIZE nameString (Elem (fromList [1])) NoMarker)))
              (Cons (ETMandatory (NamedType "familyName" Nothing nameString)) Nil))))


t = VisibleString "Director"

empNumber
    = TYPEASS "EmployeeNumber" (Just (Application, 2, Implicit)) INTEGER

num = 51

date
    = TYPEASS "Date" (Just (Application, 3, Implicit))
        (SIZE (FROM VISIBLESTRING  (VisibleString ['0'..'9'])) (Elem (fromList [8,9])) NoMarker)

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
            (Cons (ETMandatory (NamedType "name" Nothing name))
                (Cons (ETMandatory (NamedType "dateOfBirth" (Just (Context, 0, Explicit)) date)) Nil)))



nameString
    = TYPEASS "NameString" Nothing
        (SIZE (FROM VISIBLESTRING (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])) )
                            (Elem (fromList [1..64])) NoMarker)

empGN = VisibleString "John"

empFN = VisibleString "Smith"

empI = VisibleString "P"

emp = (empGN :*: (empI :*: (empFN :*: Empty)))


-- X691: A.4.1 Example Includes extensible type with extension addition groups.

ax
    = TYPEASS "Ax" Nothing
        (SEQUENCE
            (Cons (ETMandatory (NamedType "a" Nothing (RANGE INTEGER (Just 250) (Just 253))))
                (Cons (ETMandatory (NamedType "b" Nothing BOOLEAN))
                  (Cons (ETMandatory (NamedType "c" Nothing
                         (CHOICE
                          (ChoiceOption (NamedType "d" Nothing INTEGER)
                            (ChoiceExt
                              (ChoiceEAG
                                (ChoiceOption (NamedType "e" Nothing BOOLEAN)
                                  (ChoiceOption (NamedType "f" Nothing IA5STRING)
                                     (ChoiceEAG
                                       (ChoiceExt NoChoice))))))))))
                    (Extens
                        (Cons (ETExtMand (NamedType "" Nothing
                               (EXTADDGROUP
                                (Cons (ETExtMand (NamedType "g" Nothing (SIZE NUMERICSTRING (Elem (fromList [3])) NoMarker)))
                                     (Cons (ETOptional (NamedType "h" Nothing BOOLEAN)) Nil)))))
                            (Extens
                                (Cons (ETOptional (NamedType "i" Nothing VISIBLESTRING))
                                  (Cons (ETOptional (NamedType "j" Nothing VISIBLESTRING)) Nil)))))))))


axVal
    = (253 :*:
       (True :*:
         ((Nothing:*:
            ((Just True):*:(Nothing:*:Empty))) :*:
               ((Just (Just (NumericString "123") :*:(Just True :*: Empty))):*:
                 (Nothing :*:
                  (Nothing :*:Empty))))))

axEx = toPer ax axVal

-- Another test (including multiple range constraint)

seqType
    = TYPEASS "seqType" Nothing
        (SEQUENCE
            (Cons (ETMandatory (NamedType "e" Nothing
                (SEQUENCE
                    (Cons (ETMandatory (NamedType "x" Nothing
                            (RANGE (RANGE INTEGER (Just 2) Nothing) (Just (-2)) (Just 3))))
                        (Cons (ETMandatory (NamedType "o" Nothing INTEGER)) Nil)))))
                (Cons (ETMandatory (NamedType "b" Nothing INTEGER))
                  (Cons (ETMandatory (NamedType "a" Nothing INTEGER)) Nil))))

seqVal
    = ((3 :*:
        (3 :*:Empty)):*:
            ((-1):*:
                (0:*:Empty)))

seqTest = toPer seqType seqVal


-- Decoding

-- Tests for unconstrained INTEGERs

mUn1 = mDecodeEncode tInteger1 integer1
mUnTest1 = vInteger1 == mUn1
mUn2 = mDecodeEncode tInteger2 integer2
mUnTest2 = vInteger2 == mUn2

longUnIntegerPER1 = toPer tInteger1 longIntegerVal1
mUnUnLong1 = mDecodeEncode tInteger1 longUnIntegerPER1
mUnUnLongTest1 = longIntegerVal1 == mUnUnLong1

longUnIntegerPER2 = toPer tInteger1 longIntegerVal2
mUnUnLong2 = mDecodeEncode tInteger1 longUnIntegerPER2
mUnUnLongTest2 = longIntegerVal2 == mUnUnLong2

longUnIntegerPER3 = toPer tInteger1 longIntegerVal3
mUnUnLong3 = mDecodeEncode tInteger1 longUnIntegerPER3
mUnUnLongTest3 = longIntegerVal3 == mUnUnLong3

{-
-- Tests for constrained INTEGERs
-- ** uncompTest1 = runState (runErrorT (untoPerInt (RANGE INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0
mUncompTest1 = runState (runErrorT (mUntoPerInt (RANGE INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0

-- These tests are wrong
-- uncompTest2 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x18,0,1,1]))) 0
-- uncompTest3 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x81,0x80,0,0]))) 0


-- Tests for semi-constrained INTEGERs
-- We need to replace decodeLengthDeterminant with untoPerInt
-- ** unInteger5 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x02,0x10,0x01]))) 0
mUnInteger5 = runState (runErrorT (mUntoPerInt (RANGE INTEGER (Just (-1)) Nothing) (B.pack [0x02,0x10,0x01]))) 0
-}

mDecodeEncode :: ASNType Integer -> BitStream -> Integer
mDecodeEncode t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)
{-
mIdem :: ASNType a -> BitStream -> a
mIdem t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest = runState . runErrorT . fromPer t . B.pack . map (fromIntegral . fromNonNeg) . groupBy 8
-}

mUnSemi5 = mDecodeEncode tInteger5 integer5
mSemiTest5 = vInteger5 == mUnSemi5

mUnSemi6 = mDecodeEncode tInteger6 integer6
mSemiTest6 = vInteger6 == mUnSemi6

mUnSemi7 = mDecodeEncode tInteger7 integer7
mSemiTest7 = vInteger7 == mUnSemi7

natural = RANGE INTEGER (Just 0) Nothing

longIntegerVal1 = 256^4
longIntegerPER1 = toPer natural longIntegerVal1
mUnLong1 = mDecodeEncode natural longIntegerPER1
mUnLongTest1 = longIntegerVal1 == mUnLong1

longIntegerVal2 = 256^128
longIntegerPER2 = toPer natural longIntegerVal2
mUnLong2 = mDecodeEncode natural longIntegerPER2
mUnLongTest2 = longIntegerVal2 == mUnLong2

longIntegerVal3 = 256^(2^11)
longIntegerPER3 = toPer natural longIntegerVal3
mUnLong3 = mDecodeEncode natural longIntegerPER3
mUnLongTest3 = longIntegerVal3 == mUnLong3

mmIdem :: ASNType a -> BitStream -> a
mmIdem t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

testType3 = SEQUENCE (Cons (ETOptional (NamedType "l1" Nothing t1')) (Cons (ETOptional (NamedType "l1" Nothing t1')) Nil))
testVal3  = (Just 29):*:((Just 30):*:Empty)
testToPer3 = toPer testType3 testVal3
testFromPer3 = mmIdem testType3 testToPer3

testVal3'  = (Just 29):*:(Nothing:*:Empty)
testToPer3' = toPer testType3 testVal3'
-- Note that this gives the wrong answer as we don't yet pad the encoding to a multiple of 8 bits.
-- It's exposed because we use groupBy 8.
testFromPer3' = mmIdem testType3 testToPer3'



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

type1 = NamedType "T1" Nothing (RANGE INTEGER (Just 25) (Just 30))

type2 = NamedType "T2" Nothing (SEQUENCE (Cons (ETMandatory (NamedType "first" Nothing INTEGER)) Nil))

type3 =
   NamedType "T3" Nothing (SEQUENCE (
      Cons (ETMandatory (NamedType "first" Nothing INTEGER)) (
         Cons (ETMandatory (NamedType "second" Nothing INTEGER)) Nil)))

type7       = NamedType "T3" Nothing (SEQUENCE (Cons (ETMandatory type7First) (Cons (ETMandatory type7Second) (Cons (ETMandatory type7Nest1) Nil))))
type7First  = NamedType "first" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Second = NamedType "second" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (ETMandatory type7Fifth) (Cons (ETMandatory type7Fourth) (Cons (ETMandatory type7Nest2) Nil))))
type7Third  = NamedType "third" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Fourth = NamedType "fourth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (ETMandatory type7Fifth) (Cons (ETMandatory type7Sixth) Nil)))
type7Fifth  = NamedType "fifth" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Sixth  = NamedType "sixth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

testType7 = let NamedType _ _ t = type7Nest1 in toPer t (7:*:(11:*:((13:*:(17:*:Empty)):*:Empty)))

testType7' = let NamedType _ _ t = type7 in toPer t (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty)))

thereAndBack7 =
   let NamedType _ _ t = type7 in 
      mmIdem t (toPer t (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty))))

type8Nest1  = NamedType "nest1"  Nothing (SEQUENCE (Cons (ETMandatory type8Third) (Cons (ETMandatory type8Fourth) Nil)))
type8Third  = NamedType "third"  Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)
type8Fourth = NamedType "fourth" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)

type4 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..4])) NoMarker)

type5 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..14])) NoMarker)

type6 = NamedType "T1" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..((2^16)+1)])) NoMarker)

foo (NamedType _ _ t) =
   do h <- openFile "test" ReadMode
      b <- B.hGetContents h
      let d = runState (runErrorT (mFromPer t)) (b,0)
      case d of
         (Left e,s)  -> return (e ++ " " ++ show s)
         (Right n,s) -> return (show n ++ " " ++ show s)
