module NewTestData where

import ASNTYPE
import ConstraintGeneration

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
   x = (Val 5) :*: (Val 3) :*: Empty
   y = x :*: x :*: Empty

sibDataVariableType =
   ConstrainedType  (BuiltinType (BITSTRING [])) (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (1,214)))))))))))))))

sibDataVariableValue =
   BitString [1,1,1,1,1,1,1,1]

incompleteSIBList = BuiltinType (SEQUENCEOF sibDataVariableType)

completeSIBListConstraint :: ElementSetSpec [BitString]
completeSIBListConstraint = UnionSet (NoUnion (NoIntersection (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (1,16)))))))))))))

completeSIBList = ConstrainedType  (BuiltinType (SEQUENCEOF sibDataVariableType)) (RootOnly completeSIBListConstraint)


seqOf1Type = BuiltinType (SEQUENCEOF (BuiltinType INTEGER))
seqOf1Val  = take 1 $ repeat (Val 1)

seqOf1Constraint :: ElementSetSpec [InfInteger]
seqOf1Constraint = UnionSet (NoUnion (NoIntersection (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (1,16)))))))))))))

foo = ConstrainedType seqOf1Type (RootOnly seqOf1Constraint)

{-
INTEGER Tests
-}

tInteger1 = ReferencedType (Ref "INTEGER1") (BuiltinType INTEGER)
vInteger1 = Val 4096

v2_31 = (Val 2^31)

tInteger2 = ConstrainedType (BuiltinType INTEGER) (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (1,214))))))))
vInteger2 = Val 8

con1 = RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (V (R (250,253)))))))

axSeq = AddComponent (MandatoryComponent (NamedType "a" (ConstrainedType  (BuiltinType INTEGER) con1)))
                (AddComponent (MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN)))
                    (AddComponent (MandatoryComponent (NamedType "c" (BuiltinType (CHOICE choice1))))
                        (ExtensionMarker
                          (ExtensionAdditionGroup NoVersionNumber eag1
                           (ExtensionMarker (AddComponent (OptionalComponent (NamedType "i" (BuiltinType BMPSTRING)))
                                (AddComponent (OptionalComponent (NamedType "j" (BuiltinType PRINTABLESTRING)))
                                    EmptySequence)))))))



choice1 = ChoiceOption (NamedType "d" (BuiltinType INTEGER))
            (ChoiceExtensionMarker (ChoiceExtensionAdditionGroup NoVersionNumber
                            (ChoiceOption' (NamedType "e" (BuiltinType BOOLEAN))
                                   (ChoiceOption' (NamedType "f"  (BuiltinType IA5STRING))
                                          ChoiceExtensionMarker'))))





eag1 = AddComponent' (MandatoryComponent (NamedType "g" (ConstrainedType  (BuiltinType NUMERICSTRING) (RootOnly pac5))))
        (AddComponent' (OptionalComponent (NamedType "h" (BuiltinType BOOLEAN))) EmptySequence')

choice2 = ChoiceOption (NamedType "d" (BuiltinType INTEGER)) (ChoiceExtensionMarker EmptyChoice)

pac5 = UnionSet ( NoUnion (NoIntersection ((ElementConstraint (SZ (SC (RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (V (R (3,3))))))))))))))

choiceType1 = BuiltinType $ SEQUENCE axSeq

choiceType2 = BuiltinType $ SEQUENCE axSer

choiceType3 = BuiltinType $ CHOICE choice1

choiceType4 = BuiltinType $ CHOICE choice2

axSer = AddComponent (MandatoryComponent (NamedType "a" (ConstrainedType  (BuiltinType INTEGER) con1)))
                (AddComponent (MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN)))
                    (AddComponent (MandatoryComponent (NamedType "c" (BuiltinType BOOLEAN)))
                        (ExtensionMarker
                          (ExtensionAdditionGroup NoVersionNumber eag1
                           (ExtensionMarker (AddComponent (OptionalComponent (NamedType "i" (BuiltinType BMPSTRING)))
                                (AddComponent (OptionalComponent (NamedType "j" (BuiltinType PRINTABLESTRING)))
                                    EmptySequence)))))))


tInteger3 = ConstrainedType (BuiltinType INTEGER) (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (256,1234567))))))))
vInteger3 = Val 256


tInteger4 = ConstrainedType (BuiltinType INTEGER) (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (1,65538))))))))
vInteger4s = map Val [1, 257, 65538]

tInteger5 = ConstrainedType (BuiltinType INTEGER) (RootOnly (UnionSet (NoUnion (NoIntersection (ElementConstraint (V (R (NegInf,PosInf))))))))
