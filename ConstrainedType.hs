module ConstrainedType where

{-
The encoding is for UNALIGNED PER
-}

import Data.Monoid
import Data.List hiding (groupBy)
import Data.Bits
import Data.Char
import Control.Monad.State
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default))
import Text.PrettyPrint
import System
import IO
import Data.Int

type BitStream = [Int]

newtype IA5String = IA5String {iA5String :: String}
newtype BitString = BitString {bitString :: BitStream}

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
instance PermittedAlphabet VisibleString
-- INTEGER cannot be given permitted alphabet

class SizeConstraint a

instance SizeConstraint BitString
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
instance SizeConstraint [a]
instance SizeConstraint VisibleString
-- INTEGER cannot be given a size constraint


-- Heterogeneous lists of constrained types

data Nil = Empty
data a:*:l = a:*:l

instance Show Nil where
   show _ = error "Don't try to show something of type Nil just yet"

instance (Show a, Show l) => Show (a:*:l) where
   show _ = error "Don't try to show something of type a:*:l just yet"

data Sequence :: * -> * where
   Nil :: Sequence Nil
   Cons ::  Show a => ConstrainedType a -> Sequence l -> Sequence (a:*:l)
   ConsM ::  ConstrainedType a -> Sequence l -> Sequence ((Maybe a):*:l)
   Optional :: ConstrainedType a -> Sequence l -> Sequence ((Maybe a):*:l)
   Default :: ConstrainedType a -> a -> Sequence l -> Sequence ((Maybe a):*:l)

-- The Choice type is similar to a Sequence except that each value
-- is optional and only one value can exist at a time. Note that
-- the Choice type has no PER-visible constraints.

data Choice :: * -> * where
    NoChoice     :: Choice Nil
    ChoiceOption :: ConstrainedType a -> Choice l -> Choice ((Maybe a):*:l)

-- Type Aliases for Tag Information
type TagInfo    = (TagType, TagValue, TagPlicity)
type TagHistory = [TagInfo]
type TypeRef    = String
type Name       = String

data Extensible = Extensible

-- The major data structure itself

data ConstrainedType :: * -> * where
   TYPEASS         :: TypeRef -> Maybe TagInfo -> ConstrainedType a -> ConstrainedType a
   NAMEDTYPE       :: Name -> Maybe TagInfo -> ConstrainedType a -> ConstrainedType a
   EXTENSIBLE      :: ConstrainedType Extensible
   EXTADDGROUP     :: Sequence a -> ConstrainedType a
   BOOLEAN         :: ConstrainedType Bool
   INTEGER         :: ConstrainedType Integer
--   ENUMERATED      :: ConstrainedType Enumerated
   BITSTRING       :: ConstrainedType BitString
   PRINTABLESTRING :: ConstrainedType PrintableString
   IA5STRING       :: ConstrainedType IA5String
   VISIBLESTRING   :: ConstrainedType VisibleString
   Single          :: SingleValue a => ConstrainedType a -> a -> ConstrainedType a
   Includes        :: ContainedSubtype a => ConstrainedType a -> ConstrainedType a -> ConstrainedType a
   Range           :: (Ord a, ValueRange a) => ConstrainedType a -> Maybe a -> Maybe a -> ConstrainedType a
   SEQUENCE        :: Sequence a -> ConstrainedType a
   SEQUENCEOF      :: ConstrainedType a -> ConstrainedType [a]
   SIZE            :: ConstrainedType a -> Lower -> Upper -> ConstrainedType a
-- REMOVED SizeConstraint a => from above
   SET             :: Sequence a -> ConstrainedType a
   SETOF           :: ConstrainedType a -> ConstrainedType [a]
   CHOICE          :: Choice a -> ConstrainedType a
   FROM            :: PermittedAlphabet a => ConstrainedType a
                        -> a -> ConstrainedType a
{-
   -- Regular expression constraint - ignore for now but it would be cool to do them
   -- Subtyping the content of an OCTET STRING - ignore for now
   -- Constraint combinations
   -- Note that we don't need intersections - we need a longer explanation for this
   Union        :: ConstrainedType a -> ConstrainedType a -> ConstrainedType a
-}


-- dna = From PRINTABLESTRING (SingleValueAlpha (PrintableString "TAGC")) shouldn't typecheck


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
bounds (Includes t1 t2)   = (bounds t1) `mappend` (bounds t2)
bounds (Range t l u)      = (bounds t) `mappend` (Constrained l u)
bounds _                    = Constrained Nothing Nothing


-- sizeLimit returns the size limits of a value. Nothing
-- indicates no lower or upper bound.

sizeLimit :: ConstrainedType a -> Constraint Integer
sizeLimit (SIZE t l u) = sizeLimit t `mappend` Constrained l u
sizeLimit _            = Constrained Nothing Nothing

-- manageSize is a HOF used to manage the three size cases for a
-- type amenable to a size constraint.

manageSize :: (ConstrainedType a -> Integer -> Integer -> t -> t1) -> (ConstrainedType a -> t -> t1)
                -> ConstrainedType a -> t -> t1
manageSize fn1 fn2 t x
    = case p of
       Constrained (Just lb) (Just ub) ->
         fn1 t lb ub x
       Constrained (Just lb) Nothing ->
         fn2 t x
       Constrained Nothing Nothing ->
         fn2 t x
     where
      p = sizeLimit t

-- toPer is the top-level PER encoding function.

toPer :: ConstrainedType a -> a -> [Int]
toPer (TYPEASS tr tg ct) v                      = toPer ct v
toPer (NAMEDTYPE n tg ct) v                     = toPer ct v
toPer EXTENSIBLE x                              = []
toPer (EXTADDGROUP s) x                         = toPerOpen (SEQUENCE s) x
toPer t@BOOLEAN x                               = encodeBool t x
toPer t@INTEGER x                               = encodeInt t x
toPer r@(Range INTEGER l u) x                   = encodeInt r x
toPer t@BITSTRING x                             = encodeBS t x
toPer t@(SIZE BITSTRING l u) x                  = encodeBS t x
toPer (SEQUENCE s) x                            = encodeSeq s x
toPer t@(SEQUENCEOF s) x                        = encodeSO t x
toPer t@(SIZE (SEQUENCEOF c) l u) x             = encodeSO t x
toPer (SET s) x                                 = encodeSet s x
toPer t@(SETOF s) x                             = encodeSO t x
toPer t@(CHOICE c) x                            = encodeChoice c x
toPer t@VISIBLESTRING x                         = encodeVS t x
toPer t@(SIZE VISIBLESTRING l u) x              = encodeVS t x
toPer t@(FROM VISIBLESTRING pac) x              = encodeVSF t x
toPer t@(SIZE (FROM VISIBLESTRING pac) l u) x   = encodeVSF t x
toPer (SIZE (SIZE t l1 u1) l2 u2) x             = let ml = maxB l1 l2
                                                      mu = minB u1 u2
                                                  in
                                                      toPer (SIZE t ml mu) x
toPer (SIZE (TYPEASS r tg t) l u) x             = toPer (SIZE t l u) x

maxB Nothing (Just b)  = Just b
maxB (Just b) Nothing  = Just b
maxB (Just a) (Just b) = Just (max a b)
maxB _ _               = Nothing

minB Nothing (Just b)  = Just b
minB (Just b) Nothing  = Just b
minB (Just a) (Just b) = Just (min a b)
minB _ _               = Nothing


-- toPerOpen encodes an open type value. That is:
--    i. the value is encoded as ususal;
--   ii. it is padded at the end with 0s so that it has a octet-multiple length; and
--  iii. its length is added as a prefix using the fragmentation rules (10.9)

toPerOpen :: ConstrainedType a -> a -> [Int]
toPerOpen t v
    = let enc = toPer t v
          le  = length enc
          bts = le `mod` 8
          oct = le `div` 8
          n   = if bts == 0
                    then oct
                    else oct + 1
          pad = if bts == 0
                    then enc
                    else enc ++ take (8-bts) [0,0..]
      in
        encodeWithLengthDeterminant pad

-- 11 ENCODING THE BOOLEAN TYPE

encodeBool :: ConstrainedType Bool -> Bool -> BitStream
encodeBool t True = [1]
encodeBool t _    = [0]

-- 10.3 - 10.8 ENCODING THE INTEGER TYPE

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

minBits :: (Integer, Integer) -> BitStream
minBits
    = reverse . (map fromInteger) . unfoldr h
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
   reverse . (map fromInteger) . flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))


-- 10.9 General rules for encoding a length determinant
-- 10.9.4, 10.9.4.2 and 10.9.3.4 to 10.9.3.8.4.

-- encodeInsert is a HOF which manages the fragmentation and
-- encoding of a value with an unconstrained length.

encodeInsert :: (t -> [[[t1]]] -> [[a]]) -> t -> [t1] -> [a]
encodeInsert f s = concat . f s . groupBy 4 . groupBy (16*(2^10))

encodeWithLengthDeterminant :: [Int] -> [Int]
encodeWithLengthDeterminant = concat . encodeInsert unfoldr addLengths . groupBy 8

groupBy :: Int -> [t] -> [[t]]
groupBy n =
   unfoldr k
      where
         k [] = Nothing
         k p = Just (splitAt n p)

-- HOFs of use when encoding values with an unconstrained length
-- where the length value has to be interspersed with value encoding.

ulWrapper :: (Num t) => ([a] -> [a1]) -> (t1 -> [a1] -> [a1]) -> (Integer -> t -> t1)
                    -> (Integer -> [a1]) -> [[[a]]] -> Maybe ([a1], [[[a]]])
ulWrapper fn op inp lf [] = Nothing
ulWrapper fn op inp lf (x:xs)
   | l == n && lm == l1b = Just (ws x,xs)
   | l == 1 && lm <  l1b = Just (us,[])
   | otherwise           = Just (vs,[])
   where
      bl  = genericLength x
      l   = length x
      m   = x!!(l-1)
      lm  = length m
      ws  = abs1 fn op (inp bl r)
      us  = lf (genericLength m) ++ fn m
      vs  = if lm == l1b then
               ws x ++ lf 0
            else
               ws (take (l-1) x) ++ lf (genericLength m) ++ fn m
      n   = 4
      l1b = 16*(2^10)
      r = 2^6 - 1

abs1 :: (a1 -> [a]) -> (t -> [a] -> t1) -> t -> [a1] -> t1
abs1 f op x y
    = x `op` (concat . map f) y

arg1 :: Integer -> Integer -> [Int]
arg1 x y = (1:1:(minBits (x,y)))


-- addLengths adds length encoding to a sectioned bitstream. Note
-- that the input bits are unchanged as the first argument to ulWrapper is the
-- identity function.

addLengths :: [[[BitStream]]] -> Maybe ([BitStream], [[[BitStream]]])
addLengths = ulWrapper id (:) arg1 ld

ld :: Integer -> [BitStream]
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

to2sComplement :: Integer -> BitStream
to2sComplement n
   | n >= 0 = 0:(h n)
   | otherwise = minOctets (2^p + n)
   where
      p = length (h (-n-1)) + 1

g :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h :: Integer -> BitStream
h n = (reverse . map fromInteger) (flip (curry (unfoldr g)) 7 n)

-- 13 ENCODING THE ENUMERATED TYPE



-- 15 ENCODING THE BITSTRING TYPE

--

encodeBS :: ConstrainedType BitString -> BitString -> BitStream
encodeBS = manageSize encodeBSSz encodeBSNoSz


encodeBSSz :: ConstrainedType BitString -> Integer -> Integer -> BitString -> BitStream
encodeBSSz t@(SIZE ty _ _) l u x@(BitString xs)
    = let exs = editBS l u xs
      in
        if u == 0
            then []
            else if u == l && u <= 65536
                    then exs
                    else encodeBSWithLD exs

encodeBSWithLD  = encodeInsert insertBSL INTEGER

insertBSL s = unfoldr (bsLengths s)

bsLengths t = ulWrapper (id) (++) arg1 ld2

editBS :: Integer -> Integer -> BitStream -> BitStream
editBS l u xs
    = let lxs = genericLength xs
      in if lxs < l
        then add0s (l-lxs) xs
        else
            if lxs > u
             then rem0s (lxs-u) xs
             else xs

add0s :: Integer -> BitStream -> BitStream
add0s n xs = xs ++ take (fromInteger n) [0,0..]

rem0s (n+1) xs
    = if last xs == 0
           then rem0s n (init xs)
           else error "Last value is not 0"
rem0s 0 xs = xs

encodeBSNoSz :: ConstrainedType BitString -> BitString -> BitStream
encodeBSNoSz t (BitString bs)
    = let rbs = reverse bs
          rem0 = strip0s rbs
       in reverse rem0

strip0s (a:r)
    = if a == 0
        then strip0s r
        else (a:r)
strip0s [] = []

-- 18 ENCODING THE SEQUENCE TYPE

encodeSeq :: Sequence a -> a -> BitStream
encodeSeq s x
    =   let (p,es) = encodeSeqAux [] [] s x
        in  concat p ++ concat es

-- encodeSeqAux is the auxillary function for encodeSeq. When
-- encoding a sequence, one has to both encode each component and
-- produce a preamble which indicates the presence or absence of an
-- optional or default value. The first list in the result is the
-- preamble.

encodeSeqAux :: [BitStream] -> [BitStream] -> Sequence a -> a ->
    ([BitStream],[BitStream])
encodeSeqAux preamble body Nil _ = ((reverse preamble),(reverse body))
encodeSeqAux preamble body (Cons a as) (x:*:xs) =
   encodeSeqAux ([]:preamble) ((toPer a x):body) as xs
encodeSeqAux preamble body (Optional a as) (Nothing:*:xs) =
   encodeSeqAux ([0]:preamble)([]:body) as xs
encodeSeqAux preamble body (Optional a as) ((Just x):*:xs) =
   encodeSeqAux ([1]:preamble) ((toPer a x):body) as xs
encodeSeqAux preamble body (Default a d as) (Nothing:*:xs) =
   encodeSeqAux ([0]:preamble) ([]:body) as xs
encodeSeqAux preamble body (Default a d as) ((Just x):*:xs) =
   encodeSeqAux ([1]:preamble) ((toPer a x):body) as xs


-- 19. ENCODING THE SEQUENCE-OF TYPE

-- encodeSO implements the encoding of an unconstrained
-- sequence-of value. This requires both the encoding of
-- each of the components, and in most cases the encoding
-- of the length of the sequence of (which may require
-- fragmentation into 64K blocks). It uses the function manageSize
-- which manages the 3 possible size cases.

encodeSO :: ConstrainedType [a] -> [a] -> BitStream
encodeSO  = manageSize encodeSeqSz encodeSeqOf

-- encodeSeqSz encodes a size-constrained SEQUENCEOF. It uses the
-- function manageExtremes which manages the 3 upper/lower bound size value cases.

manageExtremes :: ([a] -> BitStream) -> ([a] -> BitStream) -> Integer -> Integer -> [a] -> BitStream
manageExtremes fn1 fn2 l u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
               then fn1 x
               else if u >= 65536
                   then fn2 x
                   else minBits ((genericLength x-l),range-1) ++ fn1 x

encodeSeqSz :: ConstrainedType [a] -> Integer -> Integer -> [a] -> BitStream
encodeSeqSz (SIZE ty _ _) l u x
        = manageExtremes (encodeNoL ty) (encodeSeqOf ty) l u x


encodeSeqOf :: ConstrainedType a -> a -> BitStream
encodeSeqOf (SEQUENCEOF s) xs
    = encodeWithLD s xs

-- encodeWithLD splits the components into 16K blocks, and then
-- splits these into blocks of 4 (thus a maximum of 64K in each
-- block). insertL then manages the interleaving of the length-value
-- encoding of the components.

encodeWithLD :: ConstrainedType a -> [a] -> BitStream
encodeWithLD s
    = encodeInsert insertL s

insertL :: ConstrainedType a -> [[[a]]] -> [BitStream]
insertL s = unfoldr (soLengths s)


-- soLengths adds length values to encodings of SEQUENCEOF
-- components.

soLengths :: ConstrainedType a -> [[[a]]] -> Maybe (BitStream, [[[a]]])
soLengths t = ulWrapper (concat . map (toPer t)) (++) arg1 ld2

ld2 n
   | n <= 127       = 0:(minBits (n, 127))
   | n < 16*(2^10)  = 1:0:(minBits (n, (16*(2^10)-1)))


-- No length encoding of SEQUENCEOF

encodeNoL :: ConstrainedType a -> a -> BitStream
encodeNoL (SEQUENCEOF s) xs
    = (concat . map (toPer s)) xs


-- 20. Encoding the SET type. The encoding is the same as for a
-- SEQUENCE except that the components must be canonically ordered.
-- The ordering is based on the component's tags. Note, the
-- preamble must be reordered to match the ordering of the
-- components.

encodeSet :: Sequence a -> a -> BitStream
encodeSet s x
    =   let ts     = getTags s
            (p,es) = (encodeSeqAux [] [] s x)
            ps     = zip ts es
            pps    = zip p ps
            os     = mergesort setPred pps
            pr     = concat (map fst os)
            en     = concat (map (snd . snd) os)
        in
            pr ++ en



-- Sorting

mergesort :: (a -> a -> Bool) -> [a] -> [a]
mergesort pred [] = []
mergesort pred [x] = [x]
mergesort pred xs = merge pred (mergesort pred xs1) (mergesort pred xs2)
                             where (xs1,xs2) = split xs
split :: [a] -> ([a],[a])
split xs = splitrec xs xs []
splitrec :: [a] -> [a] -> [a] -> ([a],[a])
splitrec [] ys zs = (reverse zs, ys)
splitrec [x] ys zs = (reverse zs, ys)
splitrec (x1:x2:xs) (y:ys) zs = splitrec xs ys (y:zs)

merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge pred xs [] = xs
merge pred [] ys = ys
merge pred (x:xs) (y:ys)
    = case pred x y
        of True -> x: merge pred xs (y:ys)
           False -> y: merge pred (x:xs) ys

-- Sorting predicate and tag selector

setPred :: (BitStream,(TagInfo, BitStream)) -> (BitStream,(TagInfo, BitStream)) -> Bool
setPred (_,(t1,_)) (_,(t2,_)) = t1 < t2

tagOrder :: ConstrainedType a -> ConstrainedType a -> Bool
tagOrder x y = getTI x < getTI y

getTags :: Sequence a -> [TagInfo]
getTags Nil               = []
getTags (Cons a xs)       = getTI a : getTags xs
getTags (Optional a xs)   = getTI a : getTags xs
getTags (Default a d xs)  = getTI a : getTags xs

getTI :: ConstrainedType a -> TagInfo
getTI (TYPEASS _ (Just tg) _)   = tg
getTI (TYPEASS _ _ t)           = getTI t
getTI (NAMEDTYPE _ (Just tg) _) = tg
getTI (NAMEDTYPE _ _ t)         = getTI t
getTI INTEGER                   = (Universal,2, Explicit)
getTI (Range c _ _)             = getTI c
getTI IA5STRING                 = (Universal,22, Explicit)
getTI BITSTRING                 = (Universal, 3, Explicit)
getTI PRINTABLESTRING           = (Universal, 19, Explicit)
getTI VISIBLESTRING             = (Universal, 26, Explicit)
getTI (SEQUENCE s)              = (Universal, 16, Explicit)
getTI (SEQUENCEOF s)            = (Universal, 16, Explicit)
getTI (SET s)                   = (Universal, 17, Explicit)
getTI (SETOF s)                 = (Universal, 17, Explicit)
getTI (SIZE c _ _)              = getTI c
getTI (CHOICE c)                = (minimum . getCTags) c



-- 21. Encoding the set-of type.

-- Since we are implementing BASIC-PER (and not CANONICAL-PER) the
-- encoding is as for a sequence-of.


-- 22. Encoding the choice type.

-- encodeChoice encodes CHOICE values. It is not dissimilar to
-- encodeSet in that the possible choice components must be
-- assigned an index based on their canonical ordering. This index,
-- which starts from 0, prefixes the value encoding and is absent if
-- there is only a single choice.

encodeChoice :: Choice a -> a -> BitStream
encodeChoice c x
    =   let ts  = getCTags c
            ec  = (encodeChoiceAux [] c x)
        in
            if length ec == 1
                then concat ec
            else
                let ps  = zip ts ec
                    os  = mergesort choicePred ps
                    pps = zip [0..] os
                    fr  = (head . filter (not . nullValue)) pps
                    ls  = genericLength os
                in
                     minBits (fst fr,ls-1) ++ (snd .snd) fr

nullValue :: (Integer, (TagInfo, BitStream)) -> Bool
nullValue (f,(s,t)) = null t

getCTags :: Choice a -> [TagInfo]
getCTags NoChoice              = []
getCTags (ChoiceOption a xs)   = getTI a : getCTags xs

choicePred :: (TagInfo, BitStream) -> (TagInfo, BitStream) -> Bool
choicePred (t1,_) (t2,_) = t1 < t2


encodeChoiceAux :: [BitStream] -> Choice a -> a -> [BitStream]
encodeChoiceAux body NoChoice _ = reverse body
encodeChoiceAux body (ChoiceOption a as) (Nothing:*:xs) =
   encodeChoiceAux ([]:body) as xs
encodeChoiceAux body (ChoiceOption a as) ((Just x):*:xs) =
   encodeChoiceAux' ((toPer a x):body) as xs

encodeChoiceAux' :: [BitStream] -> Choice a -> a -> [BitStream]
encodeChoiceAux' body NoChoice _ = reverse body
encodeChoiceAux' body (ChoiceOption a as) (Nothing:*:xs) =
   encodeChoiceAux' ([]:body) as xs


-- 27. Encoding the restricted character string types (VISIBLESTRING)

encodeVS :: ConstrainedType VisibleString -> VisibleString -> BitStream
encodeVS = manageSize encodeVisSz encodeVis

encodeVisSz :: ConstrainedType VisibleString -> Integer -> Integer -> VisibleString -> BitStream
encodeVisSz t@(SIZE ty _ _) l u x@(VisibleString xs)
    = manageExtremes encS (encodeVis ty . VisibleString) l u xs

encodeVis :: ConstrainedType VisibleString -> VisibleString -> BitStream
encodeVis vs (VisibleString s)
    = encodeInsert insertLVS vs s

insertLVS :: ConstrainedType VisibleString -> [[String]] -> [BitStream]
insertLVS s = unfoldr (vsLengths s)


-- vsLengths adds lengths values to encoding of sections of
-- VISIBLESTRING.

vsLengths :: ConstrainedType VisibleString -> [[String]] -> Maybe (BitStream, [[String]])
vsLengths s = ulWrapper encS (++) arg1 ld2

encC c  = minBits ((toInteger . ord) c, 94)
encS s  = (concat . map encC) s


-- 27.5.4 Encoding of a VISIBLESTRING with a permitted alphabet
-- constraint.

encodeVSF :: ConstrainedType VisibleString -> VisibleString -> BitStream
encodeVSF = manageSize encodeVisSzF encodeVisF

encodeVisSzF :: ConstrainedType VisibleString -> Integer -> Integer -> VisibleString -> BitStream
encodeVisSzF t@(SIZE ty@(FROM cv pac)_ _) l u x@(VisibleString xs)
    = manageExtremes (encSF pac) (encodeVisF ty . VisibleString) l u xs

encodeVisF :: ConstrainedType VisibleString -> VisibleString -> BitStream
encodeVisF vs@(FROM cv pac) (VisibleString s)
    = encodeInsert (insertLVSF pac) vs s

insertLVSF :: VisibleString -> t -> [[String]] -> [BitStream]
insertLVSF p s = unfoldr (vsLengthsF s p)


-- vsLengths adds lengths values to encoding of sections of
-- VISIBLESTRING.

vsLengthsF :: t -> VisibleString -> [[String]] -> Maybe (BitStream, [[String]])
vsLengthsF s p = ulWrapper (encSF p) (++) arg1 ld2

encSF (VisibleString p) str
    = let sp  = sort p
          lp  = (toInteger. length) p
          b   = minExp 2 0 lp
          mp  = maximum p
      in
        if ord mp < 2^b -1
            then
                encS str
            else
                concat (canEnc (lp-1) sp str)


minExp n e p
    = if n^e < p
        then minExp n (e+1) p
        else e

-- Clause 38.8 in X680 (Canonical ordering of VisibleString characters)

canEnc b sp [] = []
canEnc b sp (f:r)
        = let v = (toInteger . length . findV f) sp
           in minBits (v,b) : canEnc b sp r

findV m []  = []
findV m (a:rs)
          = if m == a
                then []
                else a : findV m rs



-- Decoding

n16k = 16*(2^10)

mGetBit o xs =
   if B.null ys
      then throwError ("Unable to decode " ++ show xs ++ " at bit " ++ show o)
      else return u
   where (nBytes,nBits) = o `divMod` 8
         ys = B.drop nBytes xs
         z = B.head ys
         u = (z .&. ((2^(7 - nBits)))) `shiftR` (fromIntegral (7 - nBits))

-- Very inefficient
mGetBits o n b = mapM (flip mGetBit b) [o..o+n-1]

mDecodeWithLengthDeterminant k b =
   do n <- get
      p <- mGetBit n b
      case p of
         -- 10.9.3.6
         0 ->
            do j <- mGetBits (n+1) 7 b
               let l = fromNonNeg j
               put (n + 8 + l*k)
               mGetBits (n+8) (l*k) b
         1 ->
            do q <- mGetBit (n+1) b
               case q of
                  -- 10.9.3.7
                  0 ->
                     do j <- mGetBits (n+2) 14 b
                        let l = fromNonNeg j
                        put (n + 16 + l*k)
                        mGetBits (n+16) (l*k) b
                  1 ->
                     do j <- mGetBits (n+2) 6 b
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError ("Unable to decode " ++ show b ++ " at bit " ++ show n)
                           else do frag <- mGetBits (n+8) (fragSize*n16k*k) b
                                   put (n + 8 + fragSize*n16k*k)
                                   -- This looks like it might be quadratic in efficiency!
                                   rest <- mDecodeWithLengthDeterminant k b
                                   return (frag ++ rest)

mUntoPerInt t b =
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
                       j <- mGetBits offset (fromIntegral n) b
                       return (lb + (fromNonNeg j))
      -- 12.2.3, 10.7 Encoding of a semi-constrained whole number,
      -- 10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
      Constrained (Just lb) Nothing ->
         do o <- mDecodeWithLengthDeterminant 8 b
            return (lb + (fromNonNeg o))
      _ -> undefined
   where
      p = bounds t

from2sComplement a@(x:xs) =
   -((fromIntegral x)*(2^(l-1))) + sum (zipWith (*) (map fromIntegral xs) ys)
   where
      l = genericLength a
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

mFromPerSeq :: (MonadState Int64 m, MonadError [Char] m) => Sequence a -> B.ByteString -> m a
mFromPerSeq Nil _ = return Empty
mFromPerSeq (Cons t ts) bs =
   do x  <- fromPer t bs
      xs <- mFromPerSeq ts bs
      return (x:*:xs)

fromPer :: (MonadState Int64 m, MonadError [Char] m) => ConstrainedType a -> B.ByteString -> m a
fromPer t@INTEGER x                 = mUntoPerInt t x
fromPer r@(Range INTEGER l u) x     = mUntoPerInt r x
fromPer (SEQUENCE s) x              = mFromPerSeq s x



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


t0 = INTEGER
t01 = INTEGER
t02 = INTEGER
t03 = INTEGER
t04 = INTEGER
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
t11 = CHOICE (ChoiceOption t0 (ChoiceOption t1 (ChoiceOption t01 (ChoiceOption t02 NoChoice))))
t12 = CHOICE (ChoiceOption t04 (ChoiceOption t03 NoChoice))

-- Unconstrained INTEGER
tInteger1 = INTEGER
vInteger1 = 4096
integer1 = toPer INTEGER 4096
integer2 = toPer (Range INTEGER Nothing (Just 65535)) 127
tInteger2 = Range INTEGER Nothing (Just 65535)
vInteger2 = 127
integer3 = toPer (Range INTEGER Nothing (Just 65535)) (-128)
integer4 = toPer (Range INTEGER Nothing (Just 65535)) 128


-- Semi-constrained INTEGER

tInteger5 = Range INTEGER (Just (-1)) Nothing
vInteger5 = 4096
integer5  = toPer (Range INTEGER (Just (-1)) Nothing) 4096
tInteger6 = Range INTEGER (Just 1) Nothing
vInteger6 = 127
integer6  = toPer (Range INTEGER (Just 1) Nothing) 127
tInteger7 = Range INTEGER (Just 0) Nothing
vInteger7 = 128
integer7  = toPer (Range INTEGER (Just 0) Nothing) 128

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

-- BITSTRING

bsTest1 = toPer BITSTRING (BitString [1,1,0,0,0,1,0,0,0,0])

-- Size-constrained BITSTRING

bsTest2 = toPer (SIZE BITSTRING (Just 7) (Just 7)) (BitString [1,1,0,0,0,1,0,0,0,0])
bsTest3 = toPer (SIZE BITSTRING (Just 12) (Just 15)) (BitString [1,1,0,0,0,1,0,0,0,0])


-- SEQUENCE
test1 = toPer (SEQUENCE (Cons (SEQUENCE (Cons t1 Nil)) Nil)) ((27:*:Empty):*:Empty)
test2 = toPer (SEQUENCE (Cons t1 (Cons t1 Nil))) (29:*:(30:*:Empty))
test2a = encodeSeqAux [] [] (Cons t1 (Cons t1 Nil)) (29:*:(30:*:Empty))
test20 = toPer (SEQUENCE (Cons t1 (Cons t1 (Cons t1 Nil)))) (29:*:(30:*:(26:*:Empty)))
test3 = toPer (SEQUENCE (Optional t1 (Optional t1 Nil))) ((Just 29):*:((Just 30):*:Empty))
test3a = encodeSeqAux [] [] (Optional t1 (Optional t1 Nil)) ((Just 29):*:((Just 30):*:Empty))
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

-- SET tests

test17  = toPer (SET (Cons t1 (Cons t0 Nil))) (27 :*: (5 :*: Empty))
test17a = toPer (SEQUENCE (Cons t1 (Cons t0 Nil))) (27 :*: (5 :*: Empty))
test17b = encodeSeqAux [] [] (Cons t1 (Cons t0 Nil)) (27 :*: (5 :*: Empty))

test18  = toPer (SET (Optional t1 (Optional t0 Nil))) ((Just 29):*:(Nothing:*:Empty))
test18a = toPer (SEQUENCE (Optional t1 (Optional t0 Nil))) ((Just 29):*:(Nothing:*:Empty))
test18b = encodeSeqAux [] [] (Optional t1 (Optional t0 Nil)) ((Just 29):*:(Nothing:*:Empty))

test19 = toPer (SET (Optional t1 (Optional t0 (Optional t01 Nil))))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))
test19a = toPer (SEQUENCE (Optional t1 (Optional t0 (Optional t01 Nil))))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))
test19b = encodeSeqAux [] [] (Optional t1 (Optional t0 (Optional t01 Nil)))
                ((Just 29):*: ((Just 19):*:(Nothing:*:Empty)))

-- CHOICE tests

test20c  = toPer (CHOICE (ChoiceOption t0 (ChoiceOption t1 (ChoiceOption t01 (ChoiceOption t02 NoChoice)))))
            (Nothing :*: (Just 27 :*: (Nothing :*: (Nothing :*: Empty))))

test21c  = toPer (CHOICE (ChoiceOption t0 NoChoice)) (Just 31 :*: Empty)

test22c
  = toPer (CHOICE (ChoiceOption t0 (ChoiceOption t12 NoChoice)))
             (Nothing :*: (Just (Just 52 :*: (Nothing :*: Empty)) :*: Empty))

test23c
    = toPer (CHOICE (ChoiceOption t11 (ChoiceOption t12 NoChoice)))
        (Just (Nothing :*: (Just 27 :*: (Nothing :*: (Nothing :*: Empty))))
            :*: (Nothing :*: Empty))

-- VISIBLESTRING tests

testvs1 = toPer VISIBLESTRING (VisibleString "Director")

-- VISIBLESTRING with permitted alphabet constraint and size constraints tests

x = (SIZE (FROM VISIBLESTRING (VisibleString ['0'..'9'])) (Just 8) (Just 8))

testvsc1 = toPer x (VisibleString "19710917")

-- X691: A.2.1 Example

prTest = toPer personnelRecord pr

pr = (emp :*: (t :*: (num :*: (hiredate :*: (sp :*: (Just cs :*: Empty))))))

personnelRecord
    = TYPEASS "PersonnelRecord" (Just (Application, 0, Implicit))
        (SET
          (Cons (NAMEDTYPE "name" Nothing name)
            (Cons (NAMEDTYPE "title" (Just (Context, 0, Explicit)) VISIBLESTRING)
              (Cons (NAMEDTYPE "number" Nothing empNumber)
                (Cons (NAMEDTYPE "dateOfHire" (Just (Context, 1, Explicit)) date)
                  (Cons (NAMEDTYPE "nameOfSpouse" (Just (Context, 2, Explicit)) name)
                    (Default (NAMEDTYPE "children" (Just (Context, 3, Implicit))
                                                             (SEQUENCEOF childInfo)) [] Nil)))))))

name
    = TYPEASS "Name" (Just (Application, 1, Implicit))
        (SEQUENCE
          (Cons (NAMEDTYPE "givenName" Nothing nameString)
            (Cons (NAMEDTYPE "initial" Nothing (SIZE nameString (Just 1) (Just 1)))
              (Cons (NAMEDTYPE "familyName" Nothing nameString) Nil))))


t = VisibleString "Director"

empNumber
    = TYPEASS "EmployeeNumber" (Just (Application, 2, Implicit)) INTEGER

num = 51

date
    = TYPEASS "Date" (Just (Application, 3, Implicit))
        (SIZE (FROM VISIBLESTRING  (VisibleString ['0'..'9'])) (Just 8) (Just 8))

hiredate = VisibleString "19710917"


spGN = VisibleString "Mary"

spI  = VisibleString "T"

spFN = VisibleString "Smith"

sp = (spGN :*: (spI :*: (spFN :*: Empty)))

c1GN = VisibleString "Ralph"
c1I  = VisibleString "T"
c1FN = VisibleString "Smith"
c1BD = VisibleString "19571111"

c2GN = VisibleString "Susan"
c2I  = VisibleString "B"
c2FN = VisibleString "Jones"
c2BD = VisibleString "19590717"

c1 = ((c1GN :*: (c1I :*: (c1FN :*: Empty))) :*: (c1BD :*: Empty))
c2 = ((c2GN :*: (c2I :*: (c2FN :*: Empty))) :*: (c2BD :*: Empty))

cs = [c1,c2]

childInfo
    = TYPEASS "ChildInformation" Nothing
        (SET
            (Cons (NAMEDTYPE "name" Nothing name)
                (Cons (NAMEDTYPE "dateOfBirth" (Just (Context, 0, Explicit)) date) Nil)))



nameString
    = TYPEASS "NameString" Nothing
        (SIZE (FROM VISIBLESTRING (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])) )
                            (Just 1) (Just 64))

empGN = VisibleString "John"

empFN = VisibleString "Smith"

empI = VisibleString "P"

emp = (empGN :*: (empI :*: (empFN :*: Empty)))

-- Decoding

-- Tests for unconstrained INTEGERs

mUn1 = mDecodeEncode tInteger1 integer1
mUnTest1 = vInteger1 == mUn1
mUn2 = mDecodeEncode tInteger2 integer2
mUnTest2 = vInteger2 == mUn2

longUnIntegerPER1 = toPer tInteger1 longIntegerVal1
mUnUnLong1 = mDecodeEncode tInteger1 longUnIntegerPER1
mUnUnLongTest1 = longIntegerVal1 == mUnUnLong1

longUnIntegerPER2 = toPer tInteger1 longIntegerVal2
mUnUnLong2 = mDecodeEncode tInteger1 longUnIntegerPER2
mUnUnLongTest2 = longIntegerVal2 == mUnUnLong2

longUnIntegerPER3 = toPer tInteger1 longIntegerVal3
mUnUnLong3 = mDecodeEncode tInteger1 longUnIntegerPER3
mUnUnLongTest3 = longIntegerVal3 == mUnUnLong3

-- Tests for constrained INTEGERs
-- ** uncompTest1 = runState (runErrorT (untoPerInt (Range INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0
mUncompTest1 = runState (runErrorT (mUntoPerInt (Range INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0

-- These tests are wrong
-- uncompTest2 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x18,0,1,1]))) 0
-- uncompTest3 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x81,0x80,0,0]))) 0


-- Tests for semi-constrained INTEGERs
-- We need to replace decodeLengthDeterminant with untoPerInt
-- ** unInteger5 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x02,0x10,0x01]))) 0
mUnInteger5 = runState (runErrorT (mUntoPerInt (Range INTEGER (Just (-1)) Nothing) (B.pack [0x02,0x10,0x01]))) 0


mDecodeEncode :: ConstrainedType Integer -> BitStream -> Integer
mDecodeEncode t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest = runState . runErrorT . mUntoPerInt t . B.pack . map (fromIntegral . fromNonNeg) . groupBy 8

mIdem :: ConstrainedType a -> BitStream -> a
mIdem t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest = runState . runErrorT . fromPer t . B.pack . map (fromIntegral . fromNonNeg) . groupBy 8


mUnSemi5 = mDecodeEncode tInteger5 integer5
mSemiTest5 = vInteger5 == mUnSemi5

mUnSemi6 = mDecodeEncode tInteger6 integer6
mSemiTest6 = vInteger6 == mUnSemi6

mUnSemi7 = mDecodeEncode tInteger7 integer7
mSemiTest7 = vInteger7 == mUnSemi7

natural = Range INTEGER (Just 0) Nothing

longIntegerVal1 = 256^4
longIntegerPER1 = toPer natural longIntegerVal1
mUnLong1 = mDecodeEncode natural longIntegerPER1
mUnLongTest1 = longIntegerVal1 == mUnLong1

longIntegerVal2 = 256^128
longIntegerPER2 = toPer natural longIntegerVal2
mUnLong2 = mDecodeEncode natural longIntegerPER2
mUnLongTest2 = longIntegerVal2 == mUnLong2

longIntegerVal3 = 256^(2^11)
longIntegerPER3 = toPer natural longIntegerVal3
mUnLong3 = mDecodeEncode natural longIntegerPER3
mUnLongTest3 = longIntegerVal3 == mUnLong3

testType2 = SEQUENCE (Cons t1 (Cons t1 Nil))
testVal2  = 29:*:(30:*:Empty)
testToPer2 = toPer testType2 testVal2
testFromPer2 = mIdem testType2 testToPer2

foo =
   do h <- openFile "test" ReadMode
      b <- B.hGetContents h
      let d =  runState (runErrorT (mUntoPerInt (Range  INTEGER (Just 25) (Just 30)) b)) 0
      case d of
         (Left e,s)  -> return (e ++ " " ++ show s)
         (Right n,s) -> return (show n ++ " " ++ show s)
