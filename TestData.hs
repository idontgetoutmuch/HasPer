module TestData where

import Language.ASN1 hiding (BitString)
import ConstrainedType

type7       = NamedType "T3" Nothing (SEQUENCE (Cons (CTMandatory type7First) (Cons (CTMandatory type7Second) (Cons (CTMandatory type7Nest1) Nil))))
type7First  = NamedType "first" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Second = NamedType "second" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Fourth) (Cons (CTMandatory type7Nest2) Nil))))
type7Third  = NamedType "third" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Fourth = NamedType "fourth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Sixth) Nil)))
type7Fifth  = NamedType "fifth" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Sixth  = NamedType "sixth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

val7 = (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty)))

type8       = NamedType "T4" Nothing (SEQUENCE (Cons (CTMandatory type8First) (Cons (CTMandatory type8Second) (Cons (CTMandatory type8Nest1) Nil))))
type8First  = NamedType "first"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Second = NamedType "second" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

type8Nest1  = NamedType "nest1"  Nothing (SEQUENCE (Cons (CTMandatory type8Third) (Cons (CTMandatory type8Fourth) Nil)))
type8Third  = NamedType "third"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Fourth = NamedType "fourth" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

val8 = ((BitString (bs8 12)):*:((BitString (bs8 20)):*:(((BitString (bs8 36)):*:((BitString (bs8 52)):*:Empty)):*:Empty)))

bs8 n = take n (cycle [1,0,1,0,0,0,0,0])

type12 =
   CHOICE xs
      where
         xs = ChoiceOption c1 (ChoiceOption c2 NoChoice)
         c1 = NamedType "c1" (Just (Context,0,Implicit)) s1
         c2 = NamedType "c2" (Just (Context,1,Implicit)) s2
         s1 = SEQUENCE (Cons (CTMandatory e1) (Cons (CTMandatory e2) Nil))
         s2 = SEQUENCE (Cons (CTMandatory e3) (Cons (CTMandatory e4) Nil))
         e1 = NamedType "one" Nothing INTEGER
         e2 = NamedType "two" Nothing INTEGER
         e3 = NamedType "three" Nothing INTEGER
         e4 = NamedType "four" Nothing INTEGER

type12' = NamedType "Type12" Nothing type12

val12a = ValueC (3:*:(4:*:Empty)) (NoValueC NoValue EmptyHL)
val12b = NoValueC NoValue (ValueC (1:*:(2:*:Empty)) EmptyHL)

bitStringType1 = SIZE (SIZE (BITSTRING []) (Elem (1,2)) NoMarker) (Elem (2,2)) NoMarker 