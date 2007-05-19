{-
A third attempt to model subtyping constraints

The encoding is for UNALIGNED PER
-}

import Data.Monoid
import Data.List

data BitString = BitString
   deriving Show

newtype IA5String = IA5String {unIA5String :: String}

instance Show IA5String where
   show (IA5String x) = show x

newtype IA5Char = IA5Char {unIA5Char :: Char}

class List a b | a -> b where
   nil  :: b
   cons :: a -> b -> b

instance List IA5Char IA5String where
   nil = IA5String []
   cons x y = IA5String ((unIA5Char x):(unIA5String y))

data AlphabetConstraint :: * -> * where
   SingleValueAlpha      :: List a b => a -> AlphabetConstraint b
   RangeAlpha            :: List a b => a -> a -> AlphabetConstraint b
   UnionAlpha            :: AlphabetConstraint a -> AlphabetConstraint a -> AlphabetConstraint a

newtype PrintableString = PrintableString {unPrintableString :: String}
   deriving Show

-- X.680 (07/2002) Section 47.1 Table 9

class SingleValue a

instance SingleValue BitString
instance SingleValue IA5String
instance SingleValue PrintableString
instance SingleValue Int

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype IA5String
instance ContainedSubtype PrintableString
instance ContainedSubtype Int

class ValueRange a

-- BIT STRING cannot be given value ranges
instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange Int

class PermittedAlphabet a

-- BIT STRING cannot be given permitted alphabet
instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
-- INTEGER cannot be given permitted alphabet

class SizeConstraint a

instance SizeConstraint BitString
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
-- INTEGER cannot be given a size constraint

data ConstrainedType :: * -> * where
   INTEGER         :: ConstrainedType Int
   BITSTRING       :: ConstrainedType BitString
   PRINTABLESTRING :: ConstrainedType PrintableString
   IA5STRING       :: ConstrainedType IA5String
   Single          :: SingleValue a => ConstrainedType a -> a -> ConstrainedType a
   Includes        :: ContainedSubtype a => ConstrainedType a -> ConstrainedType a -> ConstrainedType a
   Range           :: ValueRange a => ConstrainedType a -> a -> a -> ConstrainedType a
{-
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
-}

-- dna = From PRINTABLESTRING (SingleValueAlpha (PrintableString "TAGC")) now doesn't typecheck

isExtensible :: ConstrainedType a -> Bool
isExtensible = undefined

type Upper = Maybe Int
type Lower = Maybe Int

data Constraint = Constrained Lower Upper
   deriving Show

instance Monoid Constraint where
   mempty = Constrained Nothing Nothing
   mappend x y = Constrained (g x y) (f x y)
      where
         f (Constrained _ Nothing)  (Constrained _ Nothing)  = Nothing
         f (Constrained _ Nothing)  (Constrained _ (Just y)) = Just y
         f (Constrained _ (Just x)) (Constrained _ Nothing)  = Just x
         f (Constrained _ (Just x)) (Constrained _ (Just y)) = Just (min x y)
         g (Constrained Nothing _)  (Constrained Nothing _)  = Nothing
         g (Constrained Nothing _)  (Constrained (Just y) _) = Just y
         g (Constrained (Just x) _) (Constrained Nothing _)  = Just x
         g (Constrained (Just x) _) (Constrained (Just y) _) = Just (min x y)

perConstrainedness :: ConstrainedType Int -> Constraint
perConstrainedness INTEGER = Constrained Nothing Nothing
perConstrainedness (Includes t1 t2) = 
   (perConstrainedness t1) `mappend` (perConstrainedness t2)
-- TEMPORARY just now for testing of semi-constrained
perConstrainedness (Range t l 0) =
   (perConstrainedness t) `mappend` (Constrained (Just l) Nothing)
-- END TEMPORARY
perConstrainedness (Range t l u) =
   (perConstrainedness t) `mappend` (Constrained (Just l) (Just u))

encode :: Int -> ConstrainedType Int -> [Int]
encode x t =
   case p of
      -- 10.5 Encoding of a constrained whole number
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1 in
            if range <= 1
               -- 10.5.4 
               then []
               -- 10.5.6 and 10.3 Encoding as a non-negative-binary-integer
               else reverse (map fst (k (x-lb) range))
      -- 10.7 Encoding of a semi-constrained whole number
      Constrained (Just lb) Nothing ->
         minOctets (x-lb) -- TEMPORARY there's no length yet just the value
   where
      p = perConstrainedness t
      h _ 0 = Nothing
      h 0 w = Just ((0,w `mod` 2),(0,w `div` 2))
      h n w = Just ((n `mod` 2, w `mod` 2),(n `div` 2,w `div` 2))
      k = curry (unfoldr (uncurry h))
      
-- 10.3 Encoding as a non-negative-binary-integer
-- 10.3.6
minOctets :: Int -> [Bit]
minOctets =  
   flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))

minBits = 
   ((.).(.)) (reverse . (map fst)) (curry (unfoldr (uncurry h)))
      where
         h _ 0 = Nothing
         h 0 w = Just ((0,w `mod` 2),(0,w `div` 2))
         h n w = Just ((n `mod` 2, w `mod` 2),(n `div` 2,w `div` 2))

type Bit = Int
noEncoding = []
zeroBit = 0
oneBit  = 1

-- 10.9 General rules for encoding a length determinant
-- 10.9.4
lengthDeterminant n (Constrained (Just lb) (Just ub))
-- 10.9.4.1
   | ub < 64*(2^10) = minOctets n
-- 10.9.4.2, 10.9.3.5, 10.9.3.6 Note not very efficient since we know log2 128 = 7
   | n <= 127       = zeroBit:(minBits n 127)
-- 10.9.3.7 Note not very efficient since we know log2 16*(2^10) = 14
   | n < 16*(2^10)  = oneBit:zeroBit:(minBits n (16*(2^10)-1))
-- 10.9.3.8
   where
      range = (ub - lb + 1)
   
t1 = Range INTEGER 25 30
t2 = Includes INTEGER t1
t3 = Includes t1 t1
-- TEMPORARY just now for testing of semi-constrained
t4 = Range INTEGER (-256) 0
-- END TEMPORARY
