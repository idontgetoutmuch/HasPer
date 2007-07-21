{-
A fifth attempt to model subtyping constraints

The encoding is for UNALIGNED PER
-}

import Data.Monoid
import Data.List hiding (groupBy)
import Data.Bits
import Control.Monad.State
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B

type BitStream = [Int]

data BitString = BitString
   deriving Show

newtype IA5String = IA5String {iA5String :: String}

instance Show IA5String where
   show (IA5String x) = show x

newtype IA5Char = IA5Char {iA5Char :: Char}

class List a b | a -> b where
   nil  :: b
   cons :: a -> b -> b

instance List IA5Char IA5String where
   nil = IA5String []
   cons x y = IA5String ((iA5Char x):(iA5String y))

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
instance SingleValue Integer

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype IA5String
instance ContainedSubtype PrintableString
instance ContainedSubtype Integer

class ValueRange a

-- BIT STRING cannot be given value ranges
instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange Integer

class PermittedAlphabet a

-- BIT STRING cannot be given permitted alphabet
instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
-- INTEGER cannot be given permitted alphabet

class SizeConstraint a

instance SizeConstraint BitString
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
instance SizeConstraint [a]
-- INTEGER cannot be given a size constraint

-- Heterogeneous lists of constrained types

data Nil = Empty
data a:*:l = a:*:l

data Sequence :: * -> * where
   Nil :: Sequence Nil
   Cons :: ConstrainedType a -> Sequence l -> Sequence (a:*:l)
   Optional :: ConstrainedType a -> Sequence l -> Sequence ((Maybe a):*:l)
   Default :: ConstrainedType a -> Sequence l -> Sequence (a:*:l)

-- The major data structure itself

data ConstrainedType :: * -> * where
   INTEGER         :: ConstrainedType Integer
   BITSTRING       :: ConstrainedType BitString
   PRINTABLESTRING :: ConstrainedType PrintableString
   IA5STRING       :: ConstrainedType IA5String
   Single          :: SingleValue a => ConstrainedType a -> a -> ConstrainedType a
   Includes        :: ContainedSubtype a => ConstrainedType a -> ConstrainedType a -> ConstrainedType a
   Range           :: (Ord a, ValueRange a) => ConstrainedType a -> Maybe a -> Maybe a -> ConstrainedType a
   SEQUENCE        :: Sequence a -> ConstrainedType a
   SEQUENCEOF      :: ConstrainedType a -> ConstrainedType [a]
   SIZE            :: SizeConstraint a => ConstrainedType a -> Lower -> Upper -> ConstrainedType a

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

-- dna = From PRINTABLESTRING (SingleValueAlpha (PrintableString "TAGC")) shouldn't typecheck

isExtensible :: ConstrainedType a -> Bool
isExtensible = undefined

type Upper = Maybe Integer
type Lower = Maybe Integer

data Constraint a = Constrained (Maybe a) (Maybe a)
   deriving Show

instance Ord a => Monoid (Constraint a) where
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
         g (Constrained (Just x) _) (Constrained (Just y) _) = Just (max x y)

-- bounds returns the range of a value. Nothing indicates
-- no lower or upper bound.

bounds :: Ord a => ConstrainedType a -> Constraint a
bounds INTEGER = Constrained Nothing Nothing
bounds (Includes t1 t2) =
   (bounds t1) `mappend` (bounds t2)
bounds (Range t l u) =
   (bounds t) `mappend` (Constrained l u)
bounds (SEQUENCEOF x) = Constrained Nothing Nothing
bounds (SIZE t l u) = Constrained Nothing Nothing

-- sizeLimit returns the size limits of a value. Nothing
-- indicates no lower or upper bound.

sizeLimit :: ConstrainedType a -> Constraint Integer
sizeLimit (SIZE t l u) = Constrained l u
sizeLimit _            = Constrained Nothing Nothing

-- toPer is the top-level PER encoding function.

toPer :: ConstrainedType a -> a -> BitStream
toPer INTEGER x                      = encodeInt INTEGER x
toPer r@(Range INTEGER l u) x        = encodeInt r x
toPer (SEQUENCE s) x                 = encodeSeq s x
toPer t@(SEQUENCEOF s) xs            = encodeSO t xs
toPer t@(SIZE (SEQUENCEOF c) l u) x  = encodeSO t x

-- INTEGER ENCODING 10.3 - 10.8

encodeInt :: ConstrainedType Integer -> Integer -> BitStream
encodeInt t x =
   case p of
      -- 10.5 Encoding of a constrained whole number
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1 in
            if range <= 1
               -- 10.5.4
               then []
               -- 10.5.6 and 10.3 Encoding as a non-negative-binary-integer
               else minBits ((x-lb),range-1)
      -- 12.2.3, 10.7 Encoding of a semi-constrained whole number,
      -- 10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
      Constrained (Just lb) Nothing ->
         encodeWithLengthDeterminant (minOctets (x-lb))
      -- 12.2.4, 10.8 Encoding of an unconstrained whole number, 10.8.3 and
      -- 10.4 Encoding as a 2's-complement-binary-integer
      Constrained Nothing _ ->
        encodeWithLengthDeterminant (to2sComplement x)
   where
      p = bounds t


-- minBits encodes a constrained whole number (10.5.6) in the minimum
-- number of bits required for the range (assuming the range is at least 2).

minBits :: (Integer,Integer) -> BitStream
minBits
    = map fromIntegral . reverse . unfoldr h
      where
        h (_,0) = Nothing
        h (0,w) = Just (0, (0, w `div` 2))
        h (n,w) = Just (n `mod` 2, (n `div` 2, w `div` 2))

-- minOctets is used in the encoding of a semi-constrained integer (10.7). It is encoded
-- as a non-negative-binary-integer (10.3, 10.3.6) where the offset
-- from the lower bound is encoded in the minimum number of octets, preceded by
-- (or interspersed with) the encoding of the length (using encodeWithLengthDeterminant)
-- of the octet representation of the offset. (10.7.4)

minOctets :: Integer -> BitStream
minOctets =
   map fromIntegral . reverse . flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))


-- 10.9 General rules for encoding a length determinant
-- 10.9.4, 10.9.4.2 and 10.9.3.4 to 10.9.3.8.4.
encodeWithLengthDeterminant =
   concat . concat . insertLengths . groupBy 4 . groupBy (16*(2^10)) . groupBy 8

groupBy n =
   unfoldr k
      where
         k [] = Nothing
         k p = Just (splitAt n p)

insertLengths = unfoldr k

k [] = Nothing
k (x:xs)
   | l == n && lm >= l1b = Just (ws,xs)
   | l == 1 && lm <  l1b = Just (us,[])
   | otherwise           = Just (vs,[])
   where
      l   = genericLength x
      m   = x `genericIndex` (l-1)
      lm  = genericLength m
      ws  = (1:1:(minBits (l,w6))):(concat x)
      us  = ld (genericLength m) ++ m
      vs  = if lm >= l1b then
               (1:1:(minBits (l,w6))):(concat x ++ ld 0)
            else
               ((1:1:(minBits ((l-1), w6))):(concat (genericTake (l-1) x)) ++ ld (genericLength m) ++ m)
      n   = 4
      w6  = 2^6 - 1
      l1b = 16*(2^10)

ld n
-- 10.9.4.2, 10.9.3.5, 10.9.3.6 Note not very efficient since we know log2 128 = 7
   | n <= 127       = [0:(minBits (n, 127))]
-- 10.9.3.7 Note not very efficient since we know log2 16*(2^10) = 14
   | n < 16*(2^10)  = [1:0:(minBits (n, (16*(2^10)-1)))]
-- Note there is no clause for >= 16*(2^10) as we have groupBy 16*(2^10)


-- 10.4 Encoding as a 2's-complement-binary-integer is used when
-- encoding an integer with no lower bound (10.8) as in the final
-- case of encodeInt. The encoding of the integer is accompanied
-- by the encoding of its length using encodeWithLengthDeterminant
-- (10.8.3)

to2sComplement n
   | n >= 0 = 0:(h n)
   | otherwise = minOctets (2^p + n)
   where
      p = length (h (-n-1)) + 1

g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h n = map fromIntegral (reverse (flip (curry (unfoldr g)) 7 n))


-- 18 ENCODING THE SEQUENCE TYPE

encodeSeq s x = concat (encodeSeqAux [] [] s x)

-- encodeSeqAux is the auxillary function for encodeSeq. When
-- encoding a sequence, one has to both encode each component and
-- produce a preamble which indicates the presence or absence of an
-- optional or default value.

encodeSeqAux :: [Int] -> [[Int]] -> Sequence a -> a -> [BitStream]
encodeSeqAux preamble body Nil _ = (reverse preamble):(reverse body)
encodeSeqAux preamble body (Cons a as) (x:*:xs) = encodeSeqAux preamble ((toPer a x):body) as xs
encodeSeqAux preamble body (Optional a as) (Nothing:*:xs) =
   encodeSeqAux (0:preamble) body as xs
encodeSeqAux preamble body (Optional a as) ((Just x):*:xs) =
   encodeSeqAux (1:preamble) ((toPer a x):body) as xs

-- 19. ENCODING THE SEQUENCE-OF TYPE

-- encodeSO implements the encoding of an unconstrained
-- sequence-of value. This requires both the encoding of
-- each of the components, and in most cases the encoding
-- of the length of the sequence of (which may require
-- fragmentation into 64K blocks).

encodeSO :: ConstrainedType [a] -> [a] -> BitStream
encodeSO t x
  =  case p of
       Constrained (Just lb) (Just ub) ->
         encodeSeqSz t lb ub x
       Constrained (Just lb) Nothing ->
         encodeSeqOf t x
       Constrained Nothing Nothing ->
         encodeSeqOf t x
     where
      p = sizeLimit t

encodeSeqSz :: ConstrainedType [a] -> Integer -> Integer -> [a] -> BitStream
encodeSeqSz t@(SIZE ty _ _) l u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
--19.5
               then encodeNoL ty x
               else if u >= 65536
--19.6
                   then encodeSeqOf ty x
                   else minBits ((genericLength x-l),range-1) ++ encodeNoL ty x


encodeSeqOf :: ConstrainedType a -> a -> BitStream
encodeSeqOf (SEQUENCEOF s) xs
    = encodeWithLD s xs

-- encodeWithLD splits the components into 16K blocks, and then
-- splits these into blocks of 4 (thus a maximum of 64K in each
-- block). insertL then manages the interleaving of the length-value
-- encoding of the components.

encodeWithLD :: ConstrainedType a -> [a] -> BitStream
encodeWithLD s
    = concat . insertL s . groupBy 4 . groupBy (16*(2^10))

insertL :: ConstrainedType a -> [[[a]]] -> [BitStream]
insertL s = unfoldr (sk s)

sk :: ConstrainedType a -> [[[a]]] -> Maybe (BitStream, [[[a]]])
sk t [] = Nothing
sk t (x:xs)
   | l == n && lm == l1b = Just (ws,xs)
   | l == 1 && lm <  l1b = Just (us,[])
   | otherwise           = Just (vs,[])
   where
      l   = genericLength x
      m   = x `genericIndex` (l-1)
      lm  = genericLength m
      ws  = (1:1:(minBits (l,w6)))++ (concat . map (concat . map (toPer t))) x
      us  = ld2 (genericLength m) ++ (concat . map (toPer t)) m
      vs  = if lm == l1b then
               (1:1:(minBits (l,w6)))++ (concat . map (concat . map (toPer t))) x ++ ld2 0
            else
               (1:1:(minBits ((l-1), w6)))++ (concat . map (concat . map (toPer t)))
                                            (genericTake (l-1) x) ++ ld2 (genericLength m) ++ (concat . map (toPer t)) m
      n   = 4
      w6  = 2^6 - 1
      l1b = 16*(2^10)

ld2 n
   | n <= 127       = 0:(minBits (n, 127))
   | n < 16*(2^10)  = 1:0:(minBits (n, (16*(2^10)-1)))


-- No length encoding of SEQUENCEOF

encodeNoL :: ConstrainedType a -> a -> BitStream
encodeNoL (SEQUENCEOF s) xs
    = (concat . map (toPer s)) xs

-- This currently decodes the whole thing not just the length determinant as the name would suggest!
decodeLengthDeterminant b =
   do n <- get
      let bit8 = getBit n b
      if null bit8
         then throwError ("Unable to decode " ++ show b ++ " at bit " ++ show n)
         else
            case (head bit8) of
               -- 10.9.3.6
               0 ->
                  do let l = fromNonNeg (getBits (n+1) 7 b)
                     put (n + 8 + l*8)
                     return (getBits (n+8) (l*8) b)
               1 ->
                  do let bit7 = getBit (n+1) b
                     if null bit7
                        then throwError ("Unable to decode " ++ show b ++ " at bit " ++ show n)
                        else case (head bit7) of
                                -- 10.9.3.7
                                0 ->
                                   do let l = fromNonNeg (getBits (n+2) 14 b)
                                      put (n + 16 + l*8)
                                      return (getBits (n+16) (l*8) b)
                                1 ->
                                   do let fragSize = fromNonNeg (getBits (n+2) 6 b)
                                      if fragSize <= 0 || fragSize > 4
                                         then throwError ("Unable to decode " ++ show b ++ " at bit " ++ show n)
                                         else do let frag = getBits (n+8) (fragSize*16*(2^10)*8) b
                                                 put (n + 8 + fragSize*16*(2^10)*8)
                                                 -- This looks like it might be quadratic in efficiency!
                                                 rest <- decodeLengthDeterminant b
                                                 return (frag ++ rest)
                                                 
untoPerInt t b =
   case p of
      -- 10.5 Encoding of a constrained whole number
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1
             n     = genericLength (minBits ((ub-lb),range-1)) in
            if range <= 1
               -- 10.5.4
               then return lb
               -- 10.5.6 and 10.3 Encoding as a non-negative-binary-integer
               else do offset <- get
                       put (offset + n)
                       return (lb + (fromNonNeg (getBits offset (fromIntegral n) b)))
      -- 12.2.3, 10.7 Encoding of a semi-constrained whole number,
      -- 10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
      Constrained (Just lb) Nothing ->
         -- encodeWithLengthDeterminant (minOctets (x-lb))
         undefined
      _ -> undefined
   where
      p = bounds t

-- Very inefficient
getBits o n b =
   map fromIntegral (concat (map (flip getBit b) [o..o+n-1]))

getBit o xs =
   if B.null ys
      then []
      else [u]
   where (nBytes,nBits) = o `divMod` 8
         ys = B.drop nBytes xs
         z = B.head ys
         u = (z .&. ((2^(7 - nBits)))) `shiftR` (fromIntegral (7 - nBits))

from2sComplement a@(x:xs) =
   -(x*(2^(l-1))) + sum (zipWith (*) xs ys)
   where
      l = length a
      ys = map (2^) (f (l-2))
      f 0 = [0]
      f x = x:(f (x-1))

fromNonNeg xs =
   sum (zipWith (*) (map fromIntegral xs) ys)
   where
      l = genericLength xs
      ys = map (2^) (f (l-1))
      f 0 = [0]
      f x = x:(f (x-1))

{-
FooBaz {1 2 0 0 6 3} DEFINITIONS ::=
   BEGIN
      T1 ::= INTEGER (25..30)
      Test1 ::=
         SEQUENCE {
            first  T1,
            second T1
         }
      Test2 ::=
         SEQUENCE {
            first  T1 OPTIONAL,
            second T1 OPTIONAL
         }
   END
-}

t1 = Range INTEGER (Just 25) (Just 30)
t2 = Includes INTEGER t1
t3 = Includes t1 t1
t4 = Range INTEGER (Just (-256)) Nothing
t41 = Range INTEGER (Just 0) (Just 18000)
t42 = Range INTEGER (Just 3) (Just 3)
t5 = SEQUENCE (Cons t4 (Cons t4 Nil))
t6 = SEQUENCE (Cons t1 (Cons t1 Nil))
t7 = SIZE (SEQUENCEOF t1) (Just 3) (Just 5)
t8 = SIZE (SEQUENCEOF t5) (Just 2) (Just 2)
t9 = SEQUENCE (Optional t4 (Cons t4 Nil))
t10 = SIZE (SEQUENCEOF t9) (Just 1) (Just 3)

-- Unconstrained INTEGER
integer1 = toPer INTEGER 4096
integer2 = toPer (Range INTEGER Nothing (Just 65535)) 127
integer3 = toPer (Range INTEGER Nothing (Just 65535)) (-128)
integer4 = toPer (Range INTEGER Nothing (Just 65535)) 128


-- Semi-constrained INTEGER

integer5 = toPer (Range INTEGER (Just (-1)) Nothing) 4096
integer6 = toPer (Range INTEGER (Just 1) Nothing) 127
integer7 = toPer (Range INTEGER (Just 0) Nothing) 128

-- Constrained INTEGER

integer8'1 = toPer (Range INTEGER (Just 3) (Just 6)) 3
integer8'2 = toPer (Range INTEGER (Just 3) (Just 6)) 4
integer8'3 = toPer (Range INTEGER (Just 3) (Just 6)) 5
integer8'4 = toPer (Range INTEGER (Just 3) (Just 6)) 6
integer9'1 = toPer (Range INTEGER (Just 4000) (Just 4254)) 4002
integer9'2 = toPer (Range INTEGER (Just 4000) (Just 4254)) 4006
integer10'1 = toPer (Range INTEGER (Just 4000) (Just 4255)) 4002
integer10'2 = toPer (Range INTEGER (Just 4000) (Just 4255)) 4006
integer11'1 = toPer (Range INTEGER (Just 0) (Just 32000)) 0
integer11'2 = toPer (Range INTEGER (Just 0) (Just 32000)) 31000
integer11'3 = toPer (Range INTEGER (Just 0) (Just 32000)) 32000
integer12'1 = toPer (Range INTEGER (Just 1) (Just 65538)) 1
integer12'2 = toPer (Range INTEGER (Just 1) (Just 65538)) 257
integer12'3 = toPer (Range INTEGER (Just 1) (Just 65538)) 65538



test0 = toPer t1 27



-- SEQUENCE
test1 = toPer (SEQUENCE (Cons (SEQUENCE (Cons t1 Nil)) Nil)) ((27:*:Empty):*:Empty)
test2 = toPer (SEQUENCE (Cons t1 (Cons t1 Nil))) (29:*:(30:*:Empty))
test20 = toPer (SEQUENCE (Cons t1 (Cons t1 (Cons t1 Nil)))) (29:*:(30:*:(26:*:Empty)))
test3 = toPer (SEQUENCE (Optional t1 (Optional t1 Nil))) ((Just 29):*:((Just 30):*:Empty))
petest2 = toPer (SEQUENCE (Optional t1 (Optional t1 Nil)))

test4 = petest2 ((Just 29):*:((Just 30):*:Empty))
test5 = petest2 (Nothing:*:((Just 30):*:Empty))
test6 = petest2 ((Just 29):*:(Nothing:*:Empty))
test7 = petest2 (Nothing:*:(Nothing:*:Empty))

-- SEQUENCEOF
test8 = toPer (SEQUENCEOF t1) [26,27,28,25]
test9 = toPer (SEQUENCEOF t6) [29:*:(30:*:Empty),28:*:(28:*:Empty)]
test10
    = do
        c <- return (toPer (SEQUENCEOF t41) (take (17000) [1,2..]))
        writeFile "test12.txt" (show c)

test11
    = do
        c <- return (toPer (SEQUENCEOF t42) (take (17000) [3..]))
        writeFile "test14.txt" (show c)

test12
    = do
        c <- return (toPer (SEQUENCEOF t42) (take (93000) [3..]))
        writeFile "test15.txt" (show c)

-- SIZE-CONSTRAINED SEQUENCEOF
test14 = toPer t7 [26,25,28,27]

test15 = toPer t8 [(29:*:(30:*:Empty)),((-10):*:(2:*:Empty))]

test16 = toPer t10 [(Just (-10):*:(2:*:Empty))]


uncompTest1 = runState (untoPerInt (Range INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0])) 0

-- These tests are wrong
-- uncompTest2 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x18,0,1,1]))) 0
-- uncompTest3 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x81,0x80,0,0]))) 0

unInteger5 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x02,0x10,0x01]))) 0

decodeEncode :: BitStream -> BitStream
decodeEncode x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where 
      runTest = runState . runErrorT . decodeLengthDeterminant . B.pack . map (fromIntegral . fromNonNeg) . groupBy 8

unSemi5 = decodeEncode integer5
semi5 = drop 8 integer5
semiTest5 = semi5 == unSemi5

unSemi6 = decodeEncode integer6
semi6 = drop 8 integer6
semiTest6 = semi6 == unSemi6

unSemi7 = decodeEncode integer7
semi7 = drop 8 integer7
semiTest7 = semi7 == unSemi7

-- This used to give the wrong answer presumably because we were using Int

wrong = toPer (Range INTEGER (Just 0) Nothing) (256^4)
unWrong = decodeEncode wrong
wrongTest = drop 8 wrong == unWrong

longer = toPer (Range INTEGER (Just 0) Nothing) (256^128)
unLonger = decodeEncode longer

longer1 = toPer (Range INTEGER (Just 0) Nothing) (256^(2^10))
unLonger1 = decodeEncode longer1

