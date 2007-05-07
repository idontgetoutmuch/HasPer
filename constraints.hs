import Data.List
import Data.Monoid

data NumericString = NumericString String

instance Show NumericString where
   show (NumericString x) = show x

data IA5String = IA5String String

instance Show IA5String where
   show (IA5String x) = show x

class From a

instance From NumericString
instance From IA5String

data Constraint :: * -> * where
   NoConstraint    :: Constraint a
   SingleValue     :: a -> Constraint a
   Includes        :: Type a -> Constraint a
   Range           :: Int -> Int -> Constraint Int
--    Size            :: Sized a => Int -> Constraint a
   Foo             :: Sized a => Constraint Int -> Constraint a -> Constraint a
   OtherConstraint :: Constraint () -- for now
   Union           :: [Constraint a] -> Constraint a
   Intersect       :: (Show a, Show b) => Constraint a -> Constraint b -> Constraint (a,b)

-- Remove quadratic behaviour at some point
instance Show a => Show (Constraint a) where
   show NoConstraint    = "NoConstraint"
   show (SingleValue x) = "(" ++ show x ++ ")"
   show (Includes x)    = "(INCLUDES " ++ show x ++ ")"
   show (Range x y)     = "(" ++ show x ++ ".." ++ show y ++ ")"
   show (Foo s c)       = show c ++ "^( SIZE (" ++ show s ++ ")"
   show OtherConstraint = error "OtherConstraint" -- for now
   show (Union xs)      = "(" ++ concat (intersperse "|" (map show xs)) ++ ")"
   show (Intersect x y) = show x ++ "^" ++ show y

data BitString = BitString
   deriving Show

data Type :: * -> * where
   INTEGER             :: Type Int
   BOOLEAN             :: Type Bool
   BITSTRING           :: Type BitString
   NUMERICSTRING       :: Type NumericString
   IA5STRING           :: Type IA5String
   ReferencedType      :: Type () -- for now
   ConstrainedType     :: Type a -> Constraint a -> Type a
   SizeConstrainedType :: Sized a => Type a -> Constraint Int -> Type a
   FromConstrainedType :: From a => Type a -> Constraint a -> Type a

-- Remove quadratic behaviour at some point
instance Show a => Show (Type a) where
   show INTEGER = "INTEGER"
   show BOOLEAN = "BOOLEAN"
   show BITSTRING = "BIT STRING"
   show NUMERICSTRING = "NumericString"
   show IA5STRING = "IA5String"
   show ReferencedType = error "ReferencedType" -- for now
   show (ConstrainedType t c) = show t ++ " " ++ show c
   show (SizeConstrainedType t c) = show t ++ " (SIZE " ++ show c ++ ")"
   show (FromConstrainedType t c) = show t ++ " (FROM " ++ show c ++ ")"

class Sized a

instance Sized BitString
instance Sized IA5String


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
      T19 ::= IA5String (FROM ("AB")^SIZE (1..2)
                        |FROM ("DE")^SIZE (3)
                        |FROM ("ABDF")^SIZE (4..5))
   END
-}

t1 = ConstrainedType INTEGER (SingleValue 3)
t2 = INTEGER
t3 = ConstrainedType (ConstrainedType INTEGER (SingleValue 3)) (Includes t2)
t4 = ConstrainedType (ConstrainedType INTEGER (SingleValue 3)) (Includes INTEGER)
t5 = ConstrainedType (ConstrainedType INTEGER (SingleValue 3)) (Includes (ConstrainedType INTEGER (SingleValue 3)))
t6 = ConstrainedType INTEGER (Range 3 6)
t7 = ConstrainedType (ConstrainedType INTEGER (Range 3 6)) (Range 4 5)
t8 = SizeConstrainedType BITSTRING (SingleValue 31)
t9 = SizeConstrainedType BITSTRING (Range 0 31)
t10 = SizeConstrainedType BITSTRING (Includes t1)
t11 = FromConstrainedType NUMERICSTRING (SingleValue (NumericString "2"))
t12 =  FromConstrainedType NUMERICSTRING (Union (map (SingleValue . NumericString . return) "42"))
t13 = ConstrainedType INTEGER (Union [SingleValue 40, SingleValue 50])
t14 = ConstrainedType INTEGER (Range 25 30)
t15 = ConstrainedType INTEGER (Union [Includes t13, Includes t14])
t19a = SizeConstrainedType (FromConstrainedType IA5STRING (Union (map (SingleValue . IA5String . return) "AB"))) (Range 1 2)
t19b = SizeConstrainedType (FromConstrainedType IA5STRING (Union (map (SingleValue . IA5String . return) "DE"))) (SingleValue 3)
t19c = SizeConstrainedType (FromConstrainedType IA5STRING (Union (map (SingleValue . IA5String . return) "ABDF"))) (Range 4 5)
-- t19 = ConstrainedType IA5STRING (Union [t19a,t19b,t19c])
t19d = Intersect (Range 4 5) (Union [SingleValue (IA5String "A"), SingleValue (IA5String "B")]) 
t19e = Foo (SingleValue 3) (SingleValue (IA5String "A"))

class Constrained a b where
   effectiveConstraint :: a b -> Constraint b

instance Constrained Constraint b where
   effectiveConstraint (SingleValue x) = SingleValue x
   effectiveConstraint (Includes x)    = effectiveConstraint x
   effectiveConstraint (Range x y)     = Range x y
   effectiveConstraint (Union xs)      = Union xs

instance Constrained Type b where
   effectiveConstraint INTEGER               = NoConstraint
   effectiveConstraint (ConstrainedType t c) = Union [effectiveConstraint t, effectiveConstraint c]

reduceInt NoConstraint = NoConstraint
reduceInt (SingleValue x) = SingleValue x
reduceInt (Range x y) = Range x y
reduceInt (Union xs) = mconcat (map reduceInt xs)
reduceInt (Includes x) = reduceInt (effectiveConstraint x)
reduceInt x = error (show x)

-- For now because we know which data constructors we know will be used
instance Monoid (Constraint Int) where
   mempty = NoConstraint
   mappend x NoConstraint                  = x
   mappend NoConstraint y                  = y
   mappend (SingleValue x) (SingleValue y) = Range (min x y) (max x y)
   mappend (SingleValue x) (Range y z)     = Range (min x y) (max x z)
   mappend (Range y z) (SingleValue x)     = Range (min x y) (max x z)
   mappend (Range u v) (Range x y)         = Range (min u x) (max v y)

test :: Type Int -> Constraint Int
test = reduceInt . effectiveConstraint

