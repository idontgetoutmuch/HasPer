module NewTestData where

import ASNTYPE

------------------------------------------------------------------------

rt1 = ReferencedType (Ref "MyType") (BuiltinType INTEGER)

v1 = Val 3

------------------------------------------------------------------------

rt3 =
   (ReferencedType (Ref "Type3") (BuiltinType (SEQUENCE (AddComponent mc3 (AddComponent mc4 EmptySequence)))))
   where 
      mc1 = MandatoryComponent (NamedType "component1" (BuiltinType INTEGER))
      mc2 = MandatoryComponent (NamedType "component2" (BuiltinType INTEGER))
      mc3 = MandatoryComponent (NamedType "component3" s1)
      mc4 = MandatoryComponent (NamedType "component4" s1)
      s1  = BuiltinType (SEQUENCE (AddComponent mc1 (AddComponent mc2 EmptySequence)))

v3 = y where
   x = (Val 5) :*: ((Val 3) :*: Empty)
   y = x :*: ( x :*: Empty)

