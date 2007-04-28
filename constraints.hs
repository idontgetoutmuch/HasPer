import Data.List

data NumericString = NumericString String

instance Show NumericString where
   show (NumericString x) = show x

class From a

instance From NumericString

data Constraint :: * -> * where
   SingleValue     :: a -> Constraint a
   Includes        :: Type a -> Constraint a
   Range           :: Int -> Int -> Constraint Int
   OtherConstraint :: Constraint () -- for now
   Union           :: [Constraint a] -> Constraint a

-- Remove quadratic behaviour at some point
instance Show a => Show (Constraint a) where
   show (SingleValue x) = "(" ++ show x ++ ")"
   show (Includes x)    = "(INCLUDES " ++ show x ++ ")"
   show (Range x y)     = "(" ++ show x ++ ".." ++ show y ++ ")"
   show OtherConstraint = error "OtherConstraint" -- for now
   show (Union xs)      = "(" ++ concat (intersperse "|" (map show xs)) ++ ")"

data BitString = BitString
   deriving Show

data Type :: * -> * where
   INTEGER             :: Type Int
   BOOLEAN             :: Type Bool
   BITSTRING           :: Type BitString
   NUMERICSTRING       :: Type NumericString
   ReferencedType      :: Type () -- for now
   ConstrainedType     :: Type a -> Constraint a -> Type a
   SizeConstrainedType :: Size a => Type a -> Constraint Int -> Type a
   FromConstrainedType :: From a => Type a -> Constraint a -> Type a

-- Remove quadratic behaviour at some point
instance Show a => Show (Type a) where
   show INTEGER = "INTEGER"
   show BOOLEAN = "BOOLEAN"
   show BITSTRING = "BIT STRING"
   show NUMERICSTRING = "NumericString"
   show ReferencedType = error "ReferencedType" -- for now
   show (ConstrainedType t c) = show t ++ " " ++ show c
   show (SizeConstrainedType t c) = show t ++ " (SIZE " ++ show c ++ ")"
   show (FromConstrainedType t c) = show t ++ " (FROM " ++ show c ++ ")"

class Size a

instance Size BitString

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
t12 = FromConstrainedType NUMERICSTRING (Union (map (SingleValue . NumericString . return) "42"))
