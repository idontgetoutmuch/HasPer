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

sibDataVariableType =
   ConstrainedType  (BuiltinType (BITSTRING [])) (RootOnly (UnionSet (IC (ATOM (E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R (1,214)))))))))))))))

sibDataVariableValue =
   BitString [1,1,1,1,1,1,1,1]

incompleteSIBList = BuiltinType (SEQUENCEOF sibDataVariableType)

completeSIBListConstraint :: ConstraintSet [BitString]
completeSIBListConstraint = UnionSet (IC (ATOM (E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R (1,16)))))))))))))

completeSIBList = ConstrainedType  (BuiltinType (SEQUENCEOF sibDataVariableType)) (RootOnly completeSIBListConstraint)


seqOf1Type = BuiltinType (SEQUENCEOF (BuiltinType INTEGER))
seqOf1Val  = take 1 $ repeat (Val 1)

seqOf1Constraint :: ConstraintSet [InfInteger]
seqOf1Constraint = UnionSet (IC (ATOM (E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R (1,16)))))))))))))

foo = ConstrainedType seqOf1Type (RootOnly seqOf1Constraint)

{-
INTEGER Tests
-}

tInteger1 = ReferencedType (Ref "INTEGER1") (BuiltinType INTEGER)
vInteger1 = Val 4096

v2_31 = (Val 2^31)