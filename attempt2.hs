{-
A second attempt to model subtyping constraints
-}

data BitString = BitString
   deriving Show

newtype IA5String = IA5String String

instance Show IA5String where
   show (IA5String x) = show x

class Sized a

instance Sized BitString
instance Sized IA5String
instance Sized PrintableString

{-
13.2 Single value constraint
13.3 Type inclusion constraint
13.4 Value range constraint
13.5 Size constraint
13.6 Alphabet constraint
13.7 Regular expression constraint
13.8 Constraint on SEQUENCE OF or SET OF elements
13.9 Constraints on SEQUENCE, SET or CHOICE components
13.10 Subtyping the content of an octet string
13.11 Constraint combinations
13.12 Constraint extensibility
13.13 User-deﬁned constraint
-}

data ConstrainedType :: * -> * where
   INTEGER      :: ConstrainedType Int
   BITSTRING    :: ConstrainedType BitString
   PRINTABLESTRING :: ConstrainedType PrintableString
   -- Single value constraint
   SingleValue  :: ConstrainedType a -> a -> ConstrainedType a
   -- Type inclusion constraint
   Includes     :: ConstrainedType a -> ConstrainedType a -> ConstrainedType a
   -- Value range constraint
   Range        :: Ranged a => ConstrainedType a -> a -> a -> ConstrainedType a
   -- Size constraint: there are two sorts modelled by SizeConstraint
   Size         :: Sized a => ConstrainedType a -> SizeConstraint -> ConstrainedType a
   -- Alphabet constraint - not quite right see note below
   From         :: PermittedAlphabet a => ConstrainedType a -> AlphabetConstraint a -> ConstrainedType a
   -- Regular expression constraint - ignore for now but it would be cool to do them
   -- Constraint on SEQUENCE OF or SET OF - ignore for now until we fix the main datatype
   -- Constraint on SEQUENCE, SET or CHOICE - ignore for now until we fix the main datatype
   -- Subtyping the content of an OCTET STRING - ignore for now
   -- Constraint combinations
   -- Note that we don't need intersections - we need a longer explanation for this
   Union        :: ConstrainedType a -> ConstrainedType a -> ConstrainedType a   

class PermittedAlphabet a where
   unString :: a -> String

instance PermittedAlphabet PrintableString
   where unString = unPrintableString

newtype PrintableString = PrintableString {unPrintableString :: String}
   deriving Show

data SizeConstraint where
   SingleValueConstraint :: Int -> SizeConstraint
   RangeConstraint       :: Int -> Int -> SizeConstraint
   IncludesConstraint    :: ConstrainedType Int -> SizeConstraint

-- This isn't quite right as you can say things like dna below
data AlphabetConstraint :: * -> * where
   SingleValueAlpha      :: a -> AlphabetConstraint a
   RangeAlpha            :: a -> a -> AlphabetConstraint a
   UnionAlpha            :: AlphabetConstraint a -> AlphabetConstraint a -> AlphabetConstraint a

class Ranged a

instance Ranged Int
instance Ranged IA5String
instance Ranged PrintableString

-- A calculus of constraints
g INTEGER y = y
g x INTEGER = x
g (SingleValue u v) (SingleValue x y) = Range (g u x ) (min v y) (max v y)
g a@(SingleValue u v) (Includes x y)  = g a (g x y)
g (Includes u v) b@(SingleValue x y)  = g (g u v) b
g (SingleValue u v) (Range x y z)     = Range (g u x) (min v y) (max v z)
g (Includes u v) (Includes x y)       = g (g u v) (g x y)

t1 = SingleValue INTEGER 3
t2 = INTEGER
t3 = Includes (SingleValue INTEGER 3) t2
t4 = Includes (SingleValue INTEGER 3) INTEGER
t5 = Includes (SingleValue INTEGER 3) (SingleValue INTEGER 3)
t6 = Range INTEGER 3 6
t7 = Range (Range INTEGER 3 6) 4 5
t8 = Size BITSTRING (SingleValueConstraint 32)
t9 = Size BITSTRING (RangeConstraint 0 31)
t10 = Size BITSTRING (IncludesConstraint t1)
t13 = Union (SingleValue INTEGER 40) (SingleValue INTEGER 50)
t14 = Range INTEGER 25 30
t15 = Union t13 t14
t16 = Union (SingleValue INTEGER 2) 
            (Union (SingleValue INTEGER 4) 
                   (Union (SingleValue INTEGER 6)
                          (Union (SingleValue INTEGER 8) (SingleValue INTEGER 10)
                          )
                   )
            )
t17 = Size PRINTABLESTRING (IncludesConstraint t16)
t19a = Size a2 (RangeConstraint 1 2)
   where
      a1 = UnionAlpha (SingleValueAlpha (PrintableString "A")) 
                      (SingleValueAlpha (PrintableString "B")) 
      a2 = From PRINTABLESTRING a1
t19b = Size a2 (SingleValueConstraint 3)
   where
      a1 = UnionAlpha (SingleValueAlpha (PrintableString "D")) 
                      (SingleValueAlpha (PrintableString "E")) 
      a2 = From PRINTABLESTRING a1
t19c = Size a3 (RangeConstraint 4 5)
   where
      a1 = UnionAlpha (SingleValueAlpha (PrintableString "A"))
                      (SingleValueAlpha (PrintableString "B"))
      a2 = UnionAlpha (SingleValueAlpha (PrintableString "D"))
                      (SingleValueAlpha (PrintableString "F"))
      a3 = From PRINTABLESTRING (UnionAlpha a1 a2)
t19 = Union t19a (Union t19b t19c)
t20 = Range t2 3 15
two = SingleValue INTEGER 2
exactly31BitsString = Size BITSTRING (SingleValueConstraint 31)
stringsOf31BitsAtTheMost = Size BITSTRING (RangeConstraint 0 31)
dna = From PRINTABLESTRING (SingleValueAlpha (PrintableString "TAGC"))
smallSeq = Size dna (SingleValueConstraint 10)
capitalAndSmall = From PRINTABLESTRING a1
   where
      a1 = UnionAlpha (RangeAlpha (PrintableString "A") (PrintableString "Z"))
                      (RangeAlpha (PrintableString "a") (PrintableString "b"))
capitalOrSmall = Includes PRINTABLESTRING (Union a1 a2)
   where
      a1 = From PRINTABLESTRING (RangeAlpha (PrintableString "A") (PrintableString "Z"))
      a2 = From PRINTABLESTRING (RangeAlpha (PrintableString "a") (PrintableString "z"))
exoticString = Includes PRINTABLESTRING (Union a1 a2)
   where
      a1 = Size PRINTABLESTRING (RangeConstraint 1 4)
      a2 = From PRINTABLESTRING (RangeAlpha (PrintableString "a") (PrintableString "c"))
{-
FooBar {1 2 0 0 6 1} DEFINITIONS ::=
   BEGIN
      T1 ::= INTEGER (3)
      T2 ::= INTEGER
      T3 ::= INTEGER (3) (T2)
      T4 ::= INTEGER (3) (INTEGER)
      T5 ::= INTEGER (3) (INTEGER (3))
      T6 ::= INTEGER (3..6)
      T7 ::= INTEGER (3..6) (4..5)
      T8 ::= BIT STRING (SIZE (32))
      T9 ::= BIT STRING (SIZE (0..31))
      T10 ::= BITSTRING (SIZE (INCLUDES T1))
      T11 ::= NumericString (FROM ("2"))
      T12 ::= NumericString (FROM ("4"|"2"))
      T13 ::= INTEGER (40|50)
      T14 ::= INTEGER (25..30)
      T15 ::= INTEGER (T13|T14)
      T16 ::= INTEGER (2|4|6|8|10)
      T17 ::= IA5String (SIZE (INCLUDES T16))
      T18 ::= OCTET STRING (SIZE (1..MAX))
      T19a ::= IA5String (FROM ("AB")^SIZE (1..2))
      T19b ::= IA5String (FROM ("DE")^SIZE (3))
      T19c ::= IA5String (FROM ("ABDF")^SIZE (4..5))
      T19f ::= IA5String (FROM ("AB"))
      T19 ::= IA5String (FROM ("AB")^SIZE (1..2)
                        |FROM ("DE")^SIZE (3)
                        |FROM ("ABDF")^SIZE (4..5))
      T20 ::= T2 (3..15)
      Two = INTEGER (2)
      Exactly31BitsString = BIT STRING (SIZE (31))
      StringsOf31BitsAtTheMost = BITSTRING (SIZE (0..31))
      Dna = PrintableString (FROM ("TAGC"))
      SmallSeq = Dna (SIZE (10))
      CapitalAndSmall = PrintableString (FROM ("A".."Z"|"a".."z"))
      CapitalOrSmall = PrintableString (FROM ("A".."Z")|FROM ("a".."z"))
      ExoticString = PrintableString (SIZE (1..4)|FROM ("abc"))
   END
-}