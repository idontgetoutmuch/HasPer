{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
                -XScopedTypeVariables 
#-}

{-# LANGUAGE NoMonomorphismRestriction #-}

module ASNTYPE where

import Data.Word
import Data.List

personnelRecord
    = BuiltinType (TAGGED (Application, 0, Implicit) (BuiltinType (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name))) .*.
                      (MandatoryComponent (NamedType "title" (BuiltinType (TAGGED (Context, 0, Explicit) (BuiltinType VISIBLESTRING))))) .*.
                        (MandatoryComponent (NamedType "number" (ReferencedType (Ref "EmpNumber") empNumber))) .*.
                          (MandatoryComponent (NamedType "dateOfHire" (BuiltinType (TAGGED (Context, 1, Explicit) (ReferencedType (Ref "Date") date))))) .*.
                            (MandatoryComponent (NamedType "nameOfSpouse" (BuiltinType (TAGGED (Context, 2, Explicit) (ReferencedType (Ref "Name") name))))) .*.
                              (DefaultComponent (NamedType "children" 
                                (BuiltinType (TAGGED (Context, 3, Implicit) (BuiltinType (SEQUENCEOF (ReferencedType (Ref "ChildInformation") childInformation)))))) []) .*.
                                            empty))))


personnelRecord31
    = BuiltinType (TAGGED (Application, 0, Implicit) (BuiltinType (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name31))) .*.
                      (MandatoryComponent (NamedType "title" (BuiltinType (TAGGED (Context, 0, Explicit) (BuiltinType VISIBLESTRING))))) .*.
                        (MandatoryComponent (NamedType "number" (ReferencedType (Ref "EmpNumber") empNumber31))) .*.
                          (MandatoryComponent (NamedType "dateOfHire" (BuiltinType (TAGGED (Context, 1, Explicit) (ReferencedType (Ref "Date") date31))))) .*.
                            (MandatoryComponent (NamedType "nameOfSpouse" (BuiltinType (TAGGED (Context, 2, Explicit) (ReferencedType (Ref "Name") name31))))) .*.
                              (OptionalComponent (NamedType "children" 
                                (BuiltinType (TAGGED (Context, 3, Implicit) 
					     (ConstrainedType (BuiltinType (SEQUENCEOF (ReferencedType (Ref "ChildInformation") childInformation31)))
					     	(EmptyExtension (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (2,2)))))))))))))))))))) .*.
                                               (ExtensionMarker  empty)))))

childInformation
    = BuiltinType
                (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name))) .*.
                        (MandatoryComponent (NamedType "dateOfBirth" (BuiltinType (TAGGED (Context, 0, Explicit) (ReferencedType (Ref "Date") date))))) .*.
                                            empty))

childInformation31
    = BuiltinType
                (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name31))) .*.
                        (MandatoryComponent (NamedType "dateOfBirth" (BuiltinType (TAGGED (Context, 0, Explicit) (ReferencedType (Ref "Date") date31))))) .*.
			   (ExtensionMarker 
			     ((OptionalComponent (NamedType "sex" 
			        (BuiltinType (TAGGED (Context, 1, Implicit) 
			           (BuiltinType (ENUMERATED (AddEnumeration (NamedNumber "male" 1) 
					        (AddEnumeration (NamedNumber "female" 2)
						(AddEnumeration (NamedNumber "unknown" 3)
						 EmptyEnumeration))))))))) .*.
                                                  empty))))

name
    = BuiltinType (TAGGED (Application, 1, Implicit) (BuiltinType (SEQUENCE
                    ((MandatoryComponent (NamedType "givenName" (ReferencedType (Ref "NameString") nameString))) .*.
                        (MandatoryComponent (NamedType "initial" 
				      (ConstrainedType (ReferencedType (Ref "NameString") nameString)
	    			        (RootOnly (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (1,1)))))))))))))))))) .*.
                            (MandatoryComponent (NamedType "familyName" (ReferencedType (Ref "NameString") nameString))) .*. empty))))

name31
    = BuiltinType (TAGGED (Application, 1, Implicit) (BuiltinType (SEQUENCE
                    ((MandatoryComponent (NamedType "givenName" (ReferencedType (Ref "NameString") nameString31''))) .*.
                        (MandatoryComponent (NamedType "initial" 
				      (ConstrainedType (ReferencedType (Ref "NameString") nameString31'')
	    			        (RootOnly (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (1,1)))))))))))))))))) .*.
                            (MandatoryComponent (NamedType "familyName" (ReferencedType (Ref "NameString") nameString31''))) .*. (ExtensionMarker  empty)))))


empNumber = BuiltinType (TAGGED (Application, 2, Implicit) (BuiltinType INTEGER))

empNumber31 = ConstrainedType (BuiltinType (TAGGED (Application, 2, Implicit) (BuiltinType INTEGER)))
	      	(EmptyExtension (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (V (R (0,9999))))))))	      
	      		      	      

date = ConstrainedType
        (BuiltinType (TAGGED (Application, 3, Implicit) (BuiltinType VISIBLESTRING)))
        (RootOnly (UnionSet (NoUnion 
           (IntersectionMark (NoIntersection
                                (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion 
                                   (NoIntersection 
                                      (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))
				(ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion 
				   (NoIntersection 
				      (ElementConstraint (V (R (8,8)))))))))))))))

date31 = ConstrainedType
        (BuiltinType (TAGGED (Application, 3, Implicit) (BuiltinType VISIBLESTRING)))
        (RootOnly (UnionSet (NoUnion 
           (IntersectionMark (NoIntersection
                                (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion 
                                   (NoIntersection 
                                      (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))
				(ElementConstraint (SZ (SC (NonEmptyExtension (UnionSet (NoUnion 
				   (NoIntersection 
				      (ElementConstraint (V (R (8,8)))))))
                                       (UnionSet (NoUnion 
				        (NoIntersection 
				       (ElementConstraint (V (R (9,20)))))))
                                       ))))))))

nameString = ConstrainedType 
               (BuiltinType VISIBLESTRING)
	       (RootOnly (UnionSet (NoUnion 
                 (IntersectionMark (NoIntersection
                                      (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion (NoIntersection 
                                               (ElementConstraint (S (SV (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])))))))))))))
				      (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion
				               (NoIntersection (ElementConstraint (V (R (1,64)))))))))))))))

nameString31 = ConstrainedType 
               (BuiltinType VISIBLESTRING)
	       (RootOnly (UnionSet (NoUnion 
                 (IntersectionMark (NoIntersection
                                      (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion (NoIntersection
                                                                                         -- FIXME: This is semantically the same
                                                                                         -- FIXME: but will not render the same
                                                                                         -- FIXME: as the example 
                                               (ElementConstraint (S (SV (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])))))))))))))
				      (ElementConstraint (SZ (SC (EmptyExtension (UnionSet (NoUnion
				               (NoIntersection (ElementConstraint (V (R (1,64)))))))))))))))

nameString31' =
   ConstrainedType (BuiltinType VISIBLESTRING)
                   (RootOnly (UnionSet (NoUnion
                     ((NoIntersection (ElementConstraint (P (FR (RootOnly (UnionSet x)))))) /\
                      (NoIntersection (ElementConstraint (SZ (SC (EmptyExtension (UnionSet y))))))))))
      where
         x = (singletonUnion . VisibleString $ ['a'..'z']) \/
             (singletonUnion . VisibleString $ ['A'..'Z']) \/
             (singletonUnion . VisibleString $ "-.")

         y = singletonUnion' (1, 64)

nameString31'' =
   ConstrainedType (BuiltinType VISIBLESTRING)
                   (RootOnly (UnionSet (NoUnion
                     ((NoIntersection (ElementConstraint (P (FR (RootOnly (UnionSet x')))))) /\
                      (NoIntersection (ElementConstraint (SZ (SC (EmptyExtension (UnionSet y))))))))))
      where
         x' = VisibleString "a" .+. VisibleString "z" \/
              VisibleString "A" .+. VisibleString "Z" \/
              (singletonUnion . VisibleString $ "-.")
         y = 1 .+. 64



singletonIntersection :: (SingleValue a) => a -> Intersections a
singletonIntersection = NoIntersection . ElementConstraint . S . SV

-- FIXME: Hopefully temporary as we should be able to unify these somehow
singletonIntersection' :: (ValueRange a) => (a, a) -> Intersections a
singletonIntersection' = NoIntersection . ElementConstraint . V . R

singletonUnion :: (SingleValue a) => a -> Unions a
singletonUnion = NoUnion . singletonIntersection

-- FIXME: Hopefully temporary as we should be able to unify these somehow
singletonUnion' :: (ValueRange a) => (a, a) -> Unions a
singletonUnion' = NoUnion . singletonIntersection'

infixl 6 \/
(\/) :: Unions a -> Unions a -> Unions a
x \/ (NoUnion y) = UnionMark x y

infixl 5 /\
(/\) :: Intersections a -> Intersections a -> Intersections a
x /\ (NoIntersection y) = IntersectionMark x y

-- FIXME: I don't think this a good choice of symbol as we already have
-- FIXME: .*. as the SEQUENCE combinator
infixl 7 .+.
x .+. y = singletonUnion' (x, y)

pr = emp :*: t :*: num :*: hiredate :*: sp :*: Just cs :*: Empty

emp = empGN :*: empI :*: empFN :*: Empty

empGN = VisibleString "John"

empFN = VisibleString "Smith"

empI = VisibleString "P"

t = VisibleString "Director"

num = Val 51

hiredate = VisibleString "19710917"

sp = spGN :*: spI :*: spFN :*: Empty

spGN = VisibleString "Mary"

spI  = VisibleString "T"

spFN = VisibleString "Smith"

cs = [c1,c2]

c1 = ((c1GN :*: (c1I :*: (c1FN :*: Empty))) :*: (c1BD :*: (c1Sex :*: Empty)))
c2 = ((c2GN :*: (c2I :*: (c2FN :*: Empty))) :*: (c2BD :*: (c2Sex :*: Empty)))

c1GN = VisibleString "Ralph"
c1I  = VisibleString "T"
c1FN = VisibleString "Smith"
c1BD = VisibleString "19571111"
c1Sex = Nothing

c2GN = VisibleString "Susan"
c2I  = VisibleString "B"
c2FN = VisibleString "Jones"
c2BD = VisibleString "19590717"
c2Sex = Just "female"

data ASNType a where
    BuiltinType     :: ASNBuiltin a -> ASNType a
    ReferencedType  :: TypeReference -> ASNType a -> ASNType a
    ConstrainedType :: ASNType a -> SubtypeConstraint a -> ASNType a


data ASNBuiltin a where
   BITSTRING       :: NamedBits -> ASNBuiltin BitString
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin InfInteger
   ENUMERATED      :: Enumerate -> ASNBuiltin Name
   OCTETSTRING     :: ASNBuiltin OctetString
   PRINTABLESTRING :: ASNBuiltin PrintableString
   IA5STRING       :: ASNBuiltin IA5String
   VISIBLESTRING   :: ASNBuiltin VisibleString
   NUMERICSTRING   :: ASNBuiltin NumericString
   UNIVERSALSTRING :: ASNBuiltin UniversalString
   BMPSTRING       :: ASNBuiltin BMPString
   NULL            :: ASNBuiltin Null
   SEQUENCE        :: Sequence a -> ASNBuiltin a
   SEQUENCEOF      :: SeqSetOf c => c a -> ASNBuiltin [a]
   SET             :: Sequence a -> ASNBuiltin a
   SETOF           :: SeqSetOf c => c a -> ASNBuiltin [a]
   CHOICE          :: Choice a -> ASNBuiltin (ExactlyOne a SelectionMade)
   TAGGED          :: TagInfo -> ASNType a -> ASNBuiltin a

class SeqSetOf c where
   splitName :: c a -> (Maybe Name, ASNType a) 

instance SeqSetOf NamedType where
   splitName (NamedType n a) = (Just n, a)

instance SeqSetOf ASNType where
   splitName a = (Nothing, a)
   

data Null = Null
    deriving Show


data InfInteger = NegInf | Val Integer | PosInf
    deriving (Show, Ord, Eq)

instance Bounded InfInteger where
   minBound = NegInf
   maxBound = PosInf

instance Num InfInteger where
   PosInf + _ = PosInf
   _ + PosInf = PosInf
   NegInf + _ = NegInf
   _ + NegInf = NegInf
   (Val x) + (Val y) = Val (x + y)
   PosInf - _ = PosInf
   _ - PosInf = NegInf
   NegInf - _ = NegInf
   _ - NegInf = PosInf
   (Val x) - (Val y) = Val (x-y)
   NegInf * NegInf = PosInf
   _ * NegInf = NegInf
   NegInf * _ = NegInf
   PosInf * _ = PosInf
   _ * PosInf = PosInf
   (Val x) * (Val y) = Val (x*y)
   fromInteger x = Val x


newtype BitString = BitString {bitString :: BitStream}
    deriving (Eq, Show)

type BitStream = [Int]

newtype OctetString = OctetString {octetString :: OctetStream}
    deriving (Eq, Show)

type Octet = Word8
type OctetStream = [Octet]

newtype IA5String = IA5String {iA5String :: String}
    deriving (Eq, Show)

newtype PrintableString = PrintableString {printableString :: String}
    deriving (Eq, Show)
newtype NumericString = NumericString {numericString :: String}
    deriving (Eq, Show)
newtype VisibleString = VisibleString {visibleString :: String}
    deriving (Eq, Show)
newtype UniversalString = UniversalString {universalString :: String}


    deriving (Eq, Show)
newtype BMPString = BMPString {bmpString :: String}
    deriving (Eq, Show)

type Name       = String
data NamedBit = NB Name Int
type NamedBits = [NamedBit]


type TagInfo    = (TagType, TagValue, TagPlicity)

data TagType = Universal | Application | Context | Private
   deriving (Eq,Show,Enum,Ord)

type TagValue = Integer

data TagPlicity = Implicit | Explicit
   deriving (Eq,Show,Ord)


newtype TypeReference = Ref {ref :: String}
  deriving (Eq, Ord)


data SubtypeConstraint a = RootOnly (ElementSetSpec a)
                            | EmptyExtension (ElementSetSpec a)
                            | NonEmptyExtension (ElementSetSpec a) (ElementSetSpec a)


data ElementSetSpec a = UnionSet (Unions a) | ComplementSet (Exclusions a)


data Unions a = NoUnion (Intersections a) | UnionMark (Unions a) (Intersections a)
data Exclusions a = EXCEPT (Element a)
data Intersections a
    = NoIntersection (IntersectionElements a) | IntersectionMark (Intersections a) (IntersectionElements a)
data IntersectionElements a
    = ElementConstraint (Element a) | ExclusionConstraint (Element a) (Exclusions a)


data Element a = S (SingleValueConstraint a) | C (ContainedSubtypeConstraint a)
                 | V (ValueRangeConstraint a) | P (PermittedAlphabetConstraint a)
                 | SZ (SizeConstraint a) | IT (InnerTypeConstraints a)
		 | Paren (ElementSetSpec a)


data SingleValueConstraint a = SingleValue a => SV a

data ContainedSubtypeConstraint a = ContainedSubtype a => Inc (ASNType a)

data ValueRangeConstraint a = ValueRange a => R (a,a)

data SizeConstraint a = Size a => SC (SubtypeConstraint InfInteger)

data PermittedAlphabetConstraint a = PermittedAlphabet a => FR (SubtypeConstraint a)

data InnerTypeConstraints a = InnerType a => WC (SubtypeConstraint a) | WCS


class SingleValue a

instance SingleValue BitString
instance SingleValue Bool
instance SingleValue InfInteger
instance SingleValue Null
instance SingleValue VisibleString
instance SingleValue PrintableString
instance SingleValue NumericString
instance SingleValue UniversalString
instance SingleValue BMPString
instance SingleValue IA5String
instance SingleValue a => SingleValue (ExactlyOne a SelectionMade)

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype InfInteger
instance ContainedSubtype VisibleString
instance ContainedSubtype PrintableString
instance ContainedSubtype NumericString
instance ContainedSubtype UniversalString
instance ContainedSubtype BMPString
instance ContainedSubtype IA5String


class ValueRange a

instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange VisibleString
instance ValueRange UniversalString
instance ValueRange BMPString
instance ValueRange InfInteger


class PermittedAlphabet a

instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
instance PermittedAlphabet NumericString
instance PermittedAlphabet VisibleString
instance PermittedAlphabet UniversalString
instance PermittedAlphabet BMPString



class Size a

instance Size [a]
instance Size IA5String
instance Size PrintableString
instance Size NumericString
instance Size VisibleString
instance Size UniversalString
instance Size BMPString
instance Size BitString
instance Size OctetString

class InnerType a

instance InnerType (Choice a)
instance InnerType  (Sequence a)
instance InnerType [a]

type SerialSubtypeConstraints a = [SubtypeConstraint a]

data BooleanConstraint = BooleanConstraint [Bool]
                                                 deriving (Show, Eq)


data IntegerConstraint = IntegerConstraint {lower :: InfInteger, upper :: InfInteger}
   deriving (Show, Eq)

data ValidIntegerConstraint = Valid [IntegerConstraint]
    deriving (Show, Eq)


data IntegerConstraintType =
   Constrained     |
   SemiConstrained |
   UnConstrained

constraintType :: IntegerConstraint -> IntegerConstraintType
constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained

unconstrained,semiconstrained,constrained :: IntegerConstraint -> Bool
unconstrained x     = (lower x) == minBound
semiconstrained x   = (upper x) == maxBound
constrained x       = not (unconstrained x || semiconstrained x)


data EnumeratedConstraint = EnumeratedConstraint [Integer]
                             deriving (Show, Eq)


data ResStringConstraint a i = ResStringConstraint a i
    deriving (Show,Eq)

data ExtensibleConstraint i = ExtensibleConstraint i i Bool
    deriving (Show, Eq)

infixr .*.

class Sequences f where
    (.*.) :: ComponentType a -> f l -> f (a :*: l)
    empty :: f Nil
 
instance Sequences Sequence where
    (.*.) = AddComponent
    empty = EmptySequence
 
instance Sequences Sequence' where
    (.*.) = AddComponent'
    empty = EmptySequence'

infixr ...

class Sequences f => ExtensibleSequences f where
    (...) :: f l -> f l
    
instance ExtensibleSequences Sequence where 
    (...) = ExtensionMarker


data Sequence a where
   EmptySequence            :: Sequence Nil
   ExtensionMarker          :: Sequence l -> Sequence l
   ExtensionAdditionGroup   :: VersionNumber -> Sequence' a -> Sequence l
                                                -> Sequence (Maybe a :*: l)
   AddComponent             :: ComponentType a -> Sequence l
                                                -> Sequence (a:*:l)

data Sequence' a where
   EmptySequence'           :: Sequence' Nil
   AddComponent'            :: ComponentType a -> Sequence' l
                                                -> Sequence' (a:*:l)

makeSequence :: Sequence' a -> Sequence a
makeSequence EmptySequence' = EmptySequence
makeSequence (AddComponent' c s) = AddComponent c (makeSequence s)

data VersionNumber = NoVersionNumber | Version Int
data Nil = Empty

infixr 5 :*:
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys

data ComponentType a where
   MandatoryComponent   :: NamedType a -> ComponentType a
   OptionalComponent    :: NamedType a -> ComponentType (Maybe a)
   DefaultComponent     :: NamedType a -> a -> ComponentType (Maybe a)
   ComponentsOf         :: ASNType a   -> ComponentType a
   ExtensionComponent   :: NamedType a -> ComponentType (Maybe a)

data NamedType a where
   NamedType :: Name -> ASNType a -> NamedType a

getCTI :: ComponentType a -> TagInfo
getCTI (MandatoryComponent (NamedType _  (BuiltinType (TAGGED t ct)))) = t
getCTI (MandatoryComponent (NamedType _  t))             = getTI t
getCTI (ExtensionComponent (NamedType _  (BuiltinType (TAGGED t ct))))   = t
getCTI (ExtensionComponent (NamedType _ t))                = getTI t
getCTI (OptionalComponent (NamedType _  (BuiltinType (TAGGED t ct))))  = t
getCTI (OptionalComponent (NamedType _  t))              = getTI t
getCTI (DefaultComponent (NamedType _  (BuiltinType (TAGGED t ct))) d) = t
getCTI (DefaultComponent (NamedType _  t) d)             = getTI t

getTI :: ASNType a -> TagInfo
getTI (BuiltinType t) = getBuiltinTI t
getTI (ConstrainedType t _) = getTI t
getTI (ReferencedType r t) = getTI t

getBuiltinTI :: ASNBuiltin a -> TagInfo
getBuiltinTI BOOLEAN            = (Universal, 1, Explicit)
getBuiltinTI INTEGER            = (Universal,2, Explicit)
getBuiltinTI (BITSTRING _)      = (Universal, 3, Explicit)
getBuiltinTI OCTETSTRING        = (Universal, 4, Explicit)
getBuiltinTI NULL               = (Universal, 5, Explicit)
getBuiltinTI PRINTABLESTRING    = (Universal, 19, Explicit)
getBuiltinTI IA5STRING          = (Universal,22, Explicit)
getBuiltinTI VISIBLESTRING      = (Universal, 26, Explicit)
getBuiltinTI NUMERICSTRING      = (Universal, 18, Explicit)
getBuiltinTI UNIVERSALSTRING    = (Universal, 28, Explicit)
getBuiltinTI BMPSTRING          = (Universal, 30, Explicit)
getBuiltinTI (SEQUENCE s)       = (Universal, 16, Explicit)
getBuiltinTI (SEQUENCEOF s)     = (Universal, 16, Explicit)
getBuiltinTI (SET s)            = (Universal, 17, Explicit)
getBuiltinTI (SETOF s)          = (Universal, 17, Explicit)
getBuiltinTI (CHOICE c)         = (minimum . fst . snd . getCTags True ([],[])) c
getBuiltinTI (TAGGED t v)       = t

type ChoiceRootTags = [TagInfo]
type ChoiceExtTags = [TagInfo]
type InRoot = Bool

getCTags :: InRoot -> (ChoiceRootTags, ChoiceExtTags) -> Choice a -> (Bool, (ChoiceRootTags, ChoiceExtTags))
getCTags b tgs EmptyChoice                             = (b, tgs)
getCTags b tgs (ChoiceExtensionMarker xs)              = getCTags (not b) tgs xs
getCTags b tgs (ChoiceExtensionAdditionGroup vn xs)    = getCTags' b tgs xs
getCTags b (r,e) (ChoiceOption (NamedType n (BuiltinType (TAGGED t a))) xs)
     | b            = getCTags b (r ++ [t], e) xs
     | otherwise    = getCTags b (r, e ++ [t]) xs
getCTags b (r,e) (ChoiceOption (NamedType n a) xs)
     | b            = getCTags b (r ++ [getTI a], e) xs
     | otherwise    = getCTags b (r, e ++ [getTI a]) xs


getCTags' :: InRoot -> (ChoiceRootTags, ChoiceExtTags) -> Choice' a -> (Bool, (ChoiceRootTags, ChoiceExtTags))
getCTags' b tgs EmptyChoice'              = (b, tgs)
getCTags' b tgs ChoiceExtensionMarker'    = (b, tgs)
getCTags' b (r,e) (ChoiceOption' (NamedType n (BuiltinType (TAGGED t a))) xs)
     | b            = getCTags' b (r ++ [t], e) xs
     | otherwise    = getCTags' b (r, e ++ [t]) xs
getCTags' b (r,e) (ChoiceOption' (NamedType n a) xs)
     | b            = getCTags' b (r ++ [getTI a], e) xs
     | otherwise    = getCTags' b (r, e ++ [getTI a]) xs

data Choice a where
    EmptyChoice                     :: Choice Nil
    ChoiceExtensionMarker           :: Choice l -> Choice l
    ChoiceExtensionAdditionGroup    :: VersionNumber -> Choice' l -> Choice l
    ChoiceOption                    :: NamedType a -> Choice l -> Choice (a:*:l)

data Choice' a where
    EmptyChoice'                    :: Choice' Nil
    ChoiceOption'                   :: NamedType a -> Choice' l -> Choice' (a:*:l)
    ChoiceExtensionMarker'          :: Choice' Nil

data ExactlyOne a l where
    EmptyList      :: ExactlyOne Nil NoSelectionMade
    AddAValue      :: a -> ExactlyOne l NoSelectionMade -> ExactlyOne (a:*:l) SelectionMade
    AddNoValue     :: NoValue a -> ExactlyOne l n -> ExactlyOne (a:*:l) n

data NoSelectionMade

data SelectionMade

data NoValue a = NoValue

instance Show (ExactlyOne Nil n) where
   show _ = "EmptyExactlyOne"

instance (Show a, Show (ExactlyOne l n)) => Show (ExactlyOne (a:*:l) n) where
   show (AddAValue x _ ) = show x
   show (AddNoValue _ xs) = show xs

instance (Eq a, Eq (ExactlyOne l SelectionMade)) => Eq (ExactlyOne (a:*:l) SelectionMade) where
   AddAValue   _ _ == AddNoValue _ _ = False
   AddNoValue _ _ == AddAValue _ _   = False
   AddNoValue _ xs == AddNoValue _ ys = xs == ys
   AddAValue x _ == AddAValue y _ = x == y

data EnumerationItem = Identifier Name
                       | NamedNumber Name Integer
								 deriving (Show, Eq) 

getName :: EnumerationItem -> Name
getName (Identifier n) = n
getName (NamedNumber n _) = n

data Enumerate = EmptyEnumeration
                 | AddEnumeration EnumerationItem Enumerate
                 | EnumerationExtensionMarker Enumerate
								 deriving (Show, Eq)


assignIndex :: Enumerate -> (Bool, [Integer])
assignIndex en
    = let (b,ns) = assignNumber en False []
          sls = sort ns
      in
        (b, positions ns sls)

assignNumber :: Enumerate -> Bool -> [Integer] -> (Bool, [Integer])
assignNumber en b ls
    = let nn = getNamedNumbers en
      in
        assignN ([0..] \\ nn) en b ls

assignN :: [Integer] -> Enumerate -> Bool -> [Integer] -> (Bool, [Integer])
assignN (f:xs) EmptyEnumeration b ls = (b,reverse ls)
assignN (f:xs) (AddEnumeration  (NamedNumber _ i) r)b ls = assignN (f:xs) r b (i:ls)
assignN (f:xs) (AddEnumeration  _ r) b ls = assignN xs r b (f:ls)
assignN (f:xs) (EnumerationExtensionMarker   r) b ls = (True, reverse ls)
assignN [] _ _ _ = error "No numbers to assign"

getNamedNumbers :: Enumerate -> [Integer]
getNamedNumbers EmptyEnumeration = []
getNamedNumbers (AddEnumeration  (NamedNumber _ i) r) = i:getNamedNumbers r
getNamedNumbers (AddEnumeration  _ r) = getNamedNumbers r
getNamedNumbers (EnumerationExtensionMarker   r)  = []

noEnums :: Enumerate -> Integer
noEnums EmptyEnumeration = 0
noEnums (AddEnumeration  _ r) = 1 + noEnums r
noEnums (EnumerationExtensionMarker   r)  = 0

positions [] sls = []
positions (f:r) sls
    = findN f sls : positions r sls

findN i (f:r)
    = if i == f then 0
        else 1 + findN i r
findN i []
    = error "Impossible case!"

