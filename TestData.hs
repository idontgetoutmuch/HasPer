module TestData where

import Language.ASN1
import ConstrainedType

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

