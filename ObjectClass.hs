module ObjectClass where

import ConstrainedType hiding (Cons)
import Pretty
import Text.PrettyPrint

data Mu :: * -> * -> * where
   Inl :: ObjClass ((Mu a b):*:b) -> Mu a b
   Inr :: ObjClass (a:*:(Mu a b)) -> Mu a b

data ObjClass :: * -> * where
   Singleton :: ObjClassComponent a -> ObjClass a
   Cons      :: ObjClassComponent a -> ObjClass l -> ObjClass (a:*:l)
   Lift      :: Mu a l -> ObjClass (Mu a l)   

type FieldName = String

data ObjClassComponent :: * -> * where
   OCType :: FieldName -> ObjClassComponent a
   OCFixedTypeValue :: FieldName -> ASNType a -> ObjClassComponent a
   OCVariableTypeValue :: FieldName -> ObjClassComponent a -> ObjClassComponent a
   OCFixedTypeValueSet :: FieldName -> ASNType a -> ObjClassComponent a
   OCVariableTypeValueSet :: FieldName -> ObjClassComponent a -> ObjClassComponent a
   OCInformationObject :: FieldName -> ObjClass a -> ObjClassComponent a

otherFunction1 = OCType "ArgumentType"

otherFunction2 = OCFixedTypeValue "code" INTEGER

otherFunction3 = OCType "ResultType"

otherFunction4 = OCVariableTypeValue "result-if-error" otherFunction3

otherFunction5 = OCFixedTypeValueSet "Alphabet" IA5STRING

otherFunction6 = OCVariableTypeValueSet "Suppoerted Arguments" otherFunction1

otherFunction7 = OCFixedTypeValueSet "Errors" BOOLEAN

foo = Singleton (OCInformationObject "associatedFunction" foo)

baz x = (Cons otherFunction2 (Singleton (OCInformationObject "associatedFunction" x)))

baz1 = Lift (Inr (Cons otherFunction2 (Singleton (OCInformationObject "associatedFunction" baz1))))


-- From Mark Jones
-- data Mu f = In (f (Mu f))

-- (* -> * -> *) -> * -> (* -> *)
data Sigma f a = In (f a (Sigma f a))

type Foobar = Sigma (:*:) Integer

fee = In ((3::Integer) :*: fee)

fi = In (otherFunction2 :*: fi)

-- (* -> * -> *) -> * -> * -> (* -> * -> *) -> (* -> *)
data Phi f a b g = Jn (g (f a b) (Phi f a b g))

faa = Jn ((:*:) ((:*:) (3::Integer) ('a'::Char)) faa)

data Psi a f b g = Kn (g (f a b) (Psi a f b g))

fuu = Kn ((:*:) ((:*:) (3::Integer) ('a'::Char)) fuu)

fu = Kn ((:*:) ((:*:) otherFunction3 otherFunction4) fu)

fu' = Kn ((otherFunction3 :*: otherFunction4) :*: fu')

fu'' = Kn (otherFunction3 :*: otherFunction4 :*: fu'')

data Xi f a b c = Ln (f (f (f a b) c) (Xi f a b c))

goo = Ln ('a' :*: 'b' :*: 'c' :*: goo)

gee = Ln (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: gee)

f :: Xi f (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c) -> a :*: b :*: c -> String
f = undefined

g = f gee (2 :*: IA5STRING :*: 0)

data Alpha a b c = Mn ((:*:) ((:*:) ((:*:) a b) c) (Alpha a b c))

h' :: Alpha (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c) -> a :*: b :*: c -> String
h' = undefined

gee' = Mn (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: gee')

i = h' gee' (2 :*: IA5STRING :*: 0)

data Beta a b c = Nn ((:*:) ((:*:) ((:*:) a b) c) (Maybe (Beta a b c)))

hee = Nn (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: Nothing)

hee' = Nn (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: (Just hee'))

hee'' = Nn (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: (Just hee))

hh :: Beta (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c) -> a :*: b :*: c :*: (Beta (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c)) -> String
hh = undefined

j = hh hee' (2 :*: IA5STRING :*: 0 :*: hee)

k = hh hee (2 :*: IA5STRING :*: 0 :*: undefined)

data Gamma a b c = On (Maybe ((:*:) ((:*:) ((:*:) a b) c) (Gamma a b c)))

hoo = On (Just (otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: hoo))

ff :: Gamma (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c) -> a :*: b :*: c :*: (Gamma (ObjClassComponent a) (ObjClassComponent b) (ObjClassComponent c)) -> String
ff = undefined

kk = ff hoo (2 :*: IA5STRING :*: 0 :*: (On Nothing))

-- This doesn't make sense but typechecks or does it (make sense that is)
kk1 x = ff hoo (2 :*: IA5STRING :*: 0 :*: hoo)

data G x1 x2 x3 x4 x5 x6 x7 = 
   GIn (Maybe (x1 :*: x2 :*: x3 :*: x4 :*: x5 :*: x6 :*: (G x1 x2 x3 x4 x5 x6 x7) :*: x7))

gg1 = GIn (Just (otherFunction1 :*: otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: otherFunction5 :*: otherFunction6 :*: gg1 :*: otherFunction7))

gg2 = GIn (Just (otherFunction1 :*: otherFunction2 :*: otherFunction3 :*: otherFunction4 :*: otherFunction5 :*: otherFunction6 :*: (GIn Nothing) :*: otherFunction7))

myPrint (GIn Nothing) = empty
myPrint (GIn (Just (x1 :*: x2 :*: x3 :*: x4 :*: x5 :*: x6 :*: x7 :*: x8))) =
   printObjClassComp x1 <> comma $$
   printObjClassComp x2 <> comma $$
   printObjClassComp x3 <> comma $$
   printObjClassComp x4 <> comma $$
   printObjClassComp x5 <> comma $$
   printObjClassComp x6 <> comma $$
   text "Object Class"  <> comma $$
   printObjClassComp x8

printObjClassComp (OCType fn) = text "Type" <+> text fn
printObjClassComp (OCFixedTypeValue fn t) = text "Fixed Type Value" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValue fn c) = text "Variable Type Value" <+> text fn <+> braces (printObjClassComp c)
printObjClassComp (OCFixedTypeValueSet fn t) = text "Fixed Type Value Set" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValueSet fn c) = text "Variable Type Value Set" <+> text fn <+> braces (printObjClassComp c)

{-

ATTRIBUTE ::= CLASS {
  &derivation           ATTRIBUTE OPTIONAL,
  &Type                 OPTIONAL,
  &equality-match       MATCHING-RULE OPTIONAL,
  &ordering-match       MATCHING-RULE OPTIONAL,
  &substrings-match     MATCHING-RULE OPTIONAL,
  &single-valued        BOOLEAN DEFAULT FALSE,
  &collective           BOOLEAN DEFAULT FALSE,
  &no-user-modification BOOLEAN DEFAULT FALSE,
  &usage                Attribute-Usage
                          DEFAULT userApplications,
  &id                   OBJECT IDENTIFIER UNIQUE }
WITH SYNTAX {
  [SUBTYPE OF               &derivation]
  [WITH SYNTAX              &Type]
  [EQUALITY MATCHING RULE   &equality-match]
  [ORDERING MATCHING RULE   &ordering-match]
  [SUBSTRINGS MATCHING RULE &substrings-match]
  [SINGLE VALUE             &single-valued]
  [COLLECTIVE               &collective]
  [NO USER MODIFICATION     &no-user-modification]
  [USAGE                    &usage]
   ID                   &id }

-}

data ATTRIBUTE x2 x3 = 
   AIn (Maybe ((ATTRIBUTE x2 x3) :*: x2 :*: x3))

surname = AIn (Just ((AIn Nothing) :*: ((OCType "StringType") :: ObjClassComponent IA5String) :*: (OCFixedTypeValue "id" INTEGER)))

ukResident = AIn (Just ((AIn Nothing) :*: ((OCType "Resident") :: ObjClassComponent Bool) :*: (OCFixedTypeValue "id" INTEGER)))

{-
This doesn't work

surname1 = AIn (Just (ukResident :*: ((OCType "StringType") :: ObjClassComponent IA5String) :*: (OCFixedTypeValue "id" INTEGER)))

and this doesn't help

data ATTRIBUTE1 x2 x3 = 
   A1In (Maybe ((ATTRIBUTE1 y2 y3) :*: x2 :*: x3))

-}

surname2 = Cons ((OCType "StringType") :: ObjClassComponent IA5String) (Singleton (OCFixedTypeValue "id" INTEGER))

ukResident2 = Cons ((OCType "StringType") :: ObjClassComponent Bool) (Singleton (OCFixedTypeValue "id" INTEGER))

realSurname = Cons (OCInformationObject "Foo" surname2) surname2

data UbjClass :: * where
   USingleton :: UbjClassComponent -> UbjClass
   UCons      :: UbjClassComponent -> UbjClass -> UbjClass
   
data UbjClassComponent :: * where
   UCType ::                 FieldName -> UbjClassComponent
   UCFixedTypeValue ::       FieldName -> ASNType a -> UbjClassComponent
   UCVariableTypeValue ::    FieldName -> UbjClassComponent -> UbjClassComponent
   UCFixedTypeValueSet ::    FieldName -> ASNType a -> UbjClassComponent
   UCVariableTypeValueSet :: FieldName -> UbjClassComponent -> UbjClassComponent
   UCInformationObject ::    FieldName -> UbjClass -> UbjClassComponent

oF1 = UCType "ArgumentType"

oF2 = UCFixedTypeValue "code" INTEGER

oF3 = UCType "ResultType"

oF4 = UCVariableTypeValue "result-if-error" oF3

oF5 = UCFixedTypeValueSet "Alphabet" IA5STRING

oF6 = UCVariableTypeValueSet "Supported Arguments" oF1

oF7 = UCFixedTypeValueSet "Errors" BOOLEAN

oF = UCons oF7 (UCons (UCInformationObject "associated function" oF) (UCons oF3 (UCons oF6 (UCons oF1 (UCons oF5 (USingleton oF2))))))