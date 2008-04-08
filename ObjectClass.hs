module ObjectClass where

import ConstrainedType hiding (Cons)

data ObjClass :: * -> * where
   Singleton :: ObjClassComponent a -> ObjClass a
   Cons      :: ObjClassComponent a -> ObjClass l -> ObjClass (a:*:l)
   
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

foo = Singleton (OCInformationObject "associatedFunction" foo)

baz x = (Cons otherFunction2 (Singleton (OCInformationObject "associatedFunction" x)))


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
