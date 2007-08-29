module ASNType where

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
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default), NamedType)
import Text.PrettyPrint
import System
import IO
import Data.Int
import Data.Word

-- Some type aliases and newtype declarations

type BitStream = [Int]

newtype IA5String = IA5String {iA5String :: String}

instance Show IA5String where
   show s = iA5String s

newtype BitString = BitString {bitString :: BitStream}
newtype PrintableString = PrintableString {printableString :: String}
newtype NumericString = NumericString {numericString :: String}

instance Show NumericString where
   show s = numericString s

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
instance ContainedSubtype NumericString
instance ContainedSubtype Integer

class ValueRange a

-- BIT STRING cannot be given value ranges
instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange Integer


class PermittedAlphabet a

-- BIT STRING cannot be given permitted alphabet
instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
instance PermittedAlphabet VisibleString
instance PermittedAlphabet NumericString
-- INTEGER cannot be given permitted alphabet

class SizeConstraint a

instance SizeConstraint BitString
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
instance SizeConstraint [a]
instance SizeConstraint VisibleString
instance SizeConstraint NumericString


-- Heterogeneous lists and GADTs for Sequence / Choice

data Nil = Empty
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs

-- A sequence is a collection of element types

data Sequence :: * -> * where
   Nil  :: Sequence Nil
   Extens  :: Sequence l -> Sequence l
   Cons :: Show a => ElementType a -> Sequence l -> Sequence (a:*:l)

-- An element type is either mandatory, optional, or default.
-- The second constructor ETExtMand deals with an extension
-- addition which is neither optional nor default.

data ElementType :: * -> * where
   ETMandatory :: NamedType a -> ElementType a
   ETExtMand   :: NamedType a -> ElementType (Maybe a)
   ETOptional  :: NamedType a -> ElementType (Maybe a)
   ETDefault   :: NamedType a -> a -> ElementType (Maybe a)

-- A named type associates a type with a name and (possibly)
-- a tag.

data NamedType :: * -> * where
   NamedType :: Name -> Maybe TagInfo -> ASNType a -> NamedType a

-- A choice is a collection of named types. The Choice type
-- is similar to a Sequence except that each value
-- is optional and only one value can exist at a time. Note
-- that the Choice type has no PER-visible constraints.
-- The constructors ChoiceExt and ChoiceEAG deal with
-- extension markers and extension addition groups respectively.

data Choice :: * -> * where
    NoChoice     :: Choice Nil
    ChoiceExt    :: Choice l -> Choice l
    ChoiceEAG    :: Choice l -> Choice l
    ChoiceOption :: NamedType a -> Choice l -> Choice ((Maybe a):*:l)

-- Type Aliases for Tag Information

type TagInfo    = (TagType, TagValue, TagPlicity)
type TypeRef    = String
type Name       = String


-- ASNType

data ASNType :: * -> * where
   TYPEASS         :: TypeRef -> Maybe TagInfo -> ASNType a -> ASNType a
   EXTADDGROUP     :: Sequence a -> ASNType a
   BOOLEAN         :: ASNType Bool
   INTEGER         :: ASNType Integer
--   ENUMERATED      :: ASNType Enumerated
   BITSTRING       :: ASNType BitString
   PRINTABLESTRING :: ASNType PrintableString
   IA5STRING       :: ASNType IA5String
   VISIBLESTRING   :: ASNType VisibleString
   NUMERICSTRING   :: ASNType NumericString
   SINGLE          :: SingleValue a => ASNType a -> a -> ASNType a
   INCLUDES        :: ContainedSubtype a => ASNType a -> ASNType a -> ASNType a
   RANGE           :: (Ord a, ValueRange a) => ASNType a -> Maybe a -> Maybe a -> ASNType a
   SEQUENCE        :: Sequence a -> ASNType a
   SEQUENCEOF      :: ASNType a -> ASNType [a]
   SIZE            :: ASNType a -> Lower -> Upper -> ASNType a
-- REMOVED SizeConstraint a => from above
   SET             :: Sequence a -> ASNType a
   SETOF           :: ASNType a -> ASNType [a]
   CHOICE          :: Choice a -> ASNType a
   FROM            :: PermittedAlphabet a => ASNType a -> a -> ASNType a


-- Type aliases used when defining a size-constrained value.

type Upper = Maybe Integer
type Lower = Maybe Integer

-- Type used to represent the lower and upper bounds of a range or
-- size-constrained value.

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

bounds :: Ord a => ASNType a -> Constraint a
bounds (INCLUDES t1 t2)   = (bounds t1) `mappend` (bounds t2)
bounds (RANGE t l u)      = (bounds t) `mappend` (Constrained l u)
bounds _                  = Constrained Nothing Nothing


-- sizeLimit returns the size limits of a value. Nothing
-- indicates no lower or upper bound.

sizeLimit :: ASNType a -> Constraint Integer
sizeLimit (SIZE t l u) = sizeLimit t `mappend` Constrained l u
sizeLimit _            = Constrained Nothing Nothing

-- manageSize is a HOF used to manage the three size cases for a
-- type amenable to a size constraint.

manageSize :: (ASNType a -> Integer -> Integer -> t -> t1) -> (ASNType a -> t -> t1)
                -> ASNType a -> t -> t1
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

toPer :: ASNType a -> a -> [Int]
toPer (TYPEASS tr tg ct) v                      = toPer ct v
toPer (EXTADDGROUP s) x                         = toPerOpen (SEQUENCE s) x
toPer t@BOOLEAN x                               = encodeBool t x
toPer t@INTEGER x                               = encodeInt t x
toPer r@(RANGE INTEGER l u) x                   = encodeInt r x
toPer t@BITSTRING x                             = encodeBS t x
toPer t@(SIZE BITSTRING l u) x                  = encodeBS t x
toPer (SEQUENCE s) x                            = encodeSeq s x
toPer t@(SEQUENCEOF s) x                        = encodeSO t x
toPer t@(SIZE (SEQUENCEOF c) l u) x             = encodeSO t x
toPer (SET s) x                                 = encodeSet s x
toPer t@(SETOF s) x                             = encodeSO t x
toPer t@(CHOICE c) x                            = encodeChoice c x
toPer t@VISIBLESTRING x                         = encodeVS t x
toPer t@NUMERICSTRING x                         = encodeNS t x
toPer IA5STRING x                               = []
-- IA5STRING to be encoded
toPer t@(SIZE VISIBLESTRING l u) x              = encodeVS t x
toPer t@(SIZE NUMERICSTRING l u) x              = encodeNS t x
toPer t@(FROM VISIBLESTRING pac) x              = encodeVSF t x
toPer t@(SIZE (FROM VISIBLESTRING pac) l u) x   = encodeVSF t x
toPer (SIZE (SIZE t l1 u1) l2 u2) x             = let ml = maxB l1 l2
                                                      mu = minB u1 u2
                                                  in
                                                      toPer (SIZE t ml mu) x
toPer (SIZE (TYPEASS r tg t) l u) x             = toPer (SIZE t l u) x

-- maxB and minB are used when one has a nested size-constrained
-- value.

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
-- The first case is required since an extension addition group is
-- encoded as an open type sequence and toPerOpen is always called by
-- toPer on an extension component (avoids encoding it as an open
-- type open type sequence!)

toPerOpen :: ASNType a -> a -> [Int]
toPerOpen (EXTADDGROUP s) v
    = toPerOpen (SEQUENCE s) v
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

encodeBool :: ASNType Bool -> Bool -> BitStream
encodeBool t True = [1]
encodeBool t _    = [0]

-- 10.3 - 10.8 ENCODING THE INTEGER TYPE

encodeInt :: ASNType Integer -> Integer -> BitStream
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

encodeBS :: ASNType BitString -> BitString -> BitStream
encodeBS = manageSize encodeBSSz encodeBSNoSz


encodeBSSz :: ASNType BitString -> Integer -> Integer -> BitString -> BitStream
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

encodeBSNoSz :: ASNType BitString -> BitString -> BitStream
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
    =   let ((rp,rb),(ap,ab)) = encodeSeqAux ([],[]) ([],[]) s x
        in  if null ap
          then
             concat rp ++ concat rb ++ concat ap ++ concat ab
          else
             concat rp ++ concat rb ++ lengthAdds ap ++ concat ab

-- I DON'T THINK THAT THE ELSE CASE IS FRAGMENTING CORRECTLY

-- 18.8 A length determinant of the number of extension additions is added if
-- the sequence has any extension additions declared. This is encoded as a normally
-- small length (10.9.3.4)

lengthAdds ap
    = let la = genericLength ap
       in if la <= 63
        then 0:minBits (la-1, 63) ++ concat ap
        else 1:encodeWithLengthDeterminant (minOctets la) ++ concat ap

-- encodeSeqAux is the auxillary function for encodeSeq. When
-- encoding a sequence, one has to both encode each component and
-- produce a preamble which indicates the presence or absence of an
-- optional or default value. The first list in the result is the
-- preamble. The constructor Extens indicates the sequence is
-- extensible, and the coding responsibility is passed to
-- encodeExtSeqAux (where the values are encoded as an open type).
-- Note that if another Extens occurs then reponsibility returns
-- to encodeSeqAux since this is the 2 extension marker case
-- (and what follows is in the extension root).

encodeSeqAux :: ([BitStream],[BitStream]) -> ([BitStream],[BitStream]) -> Sequence a -> a ->
    (([BitStream],[BitStream]),([BitStream],[BitStream]))
encodeSeqAux (ap,ab) (rp,rb) Nil _
    = if ((not.null) (concat ab))
        then (([1]:reverse rp,reverse rb),(reverse ap,reverse ab))
        else ((reverse rp,reverse rb),(reverse ap, reverse ab))
encodeSeqAux (ap,ab) (rp,rb) (Extens as) xs
    = encodeExtSeqAux (ap,ab) (rp,rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETMandatory (NamedType n t a)) as) (x:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETExtMand (NamedType n t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETExtMand (NamedType n t a)) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETOptional (NamedType n t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETOptional (NamedType n t a)) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([1]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETDefault (NamedType n t a) d) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (ETDefault (NamedType n t a) d) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([1]:rp,toPer a x:rb) as xs


-- encodeExtSeqAux adds the encoding of any extension additions to
-- the encoding of the extension root. If an addition is present a
-- 1 is added to a bitstream prefix and the value is encoded as an
-- open type (using toPerOpen). If an addition is not present then a
-- 0 is added to the prefix.

encodeExtSeqAux :: ([BitStream],[BitStream]) -> ([BitStream], [BitStream]) -> Sequence a -> a ->
    (([BitStream],[BitStream]),([BitStream],[BitStream]))
encodeExtSeqAux (ap,ab) (rp,rb) Nil _
    = if (length . filter (==[1])) ap > 0
                then  (([1]:reverse rp,reverse rb),(reverse ap,reverse ab))
                else  (([0]:reverse rp,reverse ab),(reverse ap,reverse ab))
encodeExtSeqAux extAdds extRoot (Extens as) xs =
   encodeSeqAux extAdds extRoot as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETExtMand (NamedType n t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETExtMand (NamedType n t a)) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETOptional (NamedType n t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETOptional (NamedType n t a)) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETDefault (NamedType n t a) d) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (ETDefault (NamedType n t a) d) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs



-- 19. ENCODING THE SEQUENCE-OF TYPE

-- encodeSO implements the encoding of an unconstrained
-- sequence-of value. This requires both the encoding of
-- each of the components, and in most cases the encoding
-- of the length of the sequence of (which may require
-- fragmentation into 64K blocks). It uses the function manageSize
-- which manages the 3 possible size cases.

encodeSO :: ASNType [a] -> [a] -> BitStream
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

encodeSeqSz :: ASNType [a] -> Integer -> Integer -> [a] -> BitStream
encodeSeqSz (SIZE ty _ _) l u x
        = manageExtremes (encodeNoL ty) (encodeSeqOf ty) l u x


encodeSeqOf :: ASNType a -> a -> BitStream
encodeSeqOf (SEQUENCEOF s) xs
    = encodeWithLD s xs

-- encodeWithLD splits the components into 16K blocks, and then
-- splits these into blocks of 4 (thus a maximum of 64K in each
-- block). insertL then manages the interleaving of the length-value
-- encoding of the components.

encodeWithLD :: ASNType a -> [a] -> BitStream
encodeWithLD s
    = encodeInsert insertL s

insertL :: ASNType a -> [[[a]]] -> [BitStream]
insertL s = unfoldr (soLengths s)


-- soLengths adds length values to encodings of SEQUENCEOF
-- components.

soLengths :: ASNType a -> [[[a]]] -> Maybe (BitStream, [[[a]]])
soLengths t = ulWrapper (concat . map (toPer t)) (++) arg1 ld2

ld2 n
   | n <= 127       = 0:(minBits (n, 127))
   | n < 16*(2^10)  = 1:0:(minBits (n, (16*(2^10)-1)))


-- No length encoding of SEQUENCEOF

encodeNoL :: ASNType a -> a -> BitStream
encodeNoL (SEQUENCEOF s) xs
    = (concat . map (toPer s)) xs


-- 20. Encoding the SET type. The encoding is the same as for a
-- SEQUENCE except that the components must be canonically ordered.
-- The ordering is based on the component's tags. Note, the
-- preamble must be reordered to match the ordering of the
-- components.


encodeSet :: Sequence a -> a -> BitStream
encodeSet s x
    =   let ts                = getTags s
            ((rp,rb),(ap,ab)) = encodeSeqAux ([],[]) ([],[]) s x
            ps                = zip ts rb
            pps               = zip rp ps
            os                = mergesort setPred pps
            pr                = concat (map fst os)
            en                = concat (map (snd . snd) os)
        in
            pr ++ en ++ concat ap ++ concat ab



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

tagOrder :: ASNType a -> ASNType a -> Bool
tagOrder x y = getTI x < getTI y


getTags :: Sequence a -> [TagInfo]
getTags Nil               = []
getTags (Extens xs)       = getTags' xs
getTags (Cons a xs)       = getETI a : getTags xs


getTags' :: Sequence a -> [TagInfo]
getTags' Nil         = []
getTags' (Extens xs) = getTags xs
getTags' (Cons a xs) = getTags' xs


getETI :: ElementType a -> TagInfo
getETI (ETMandatory (NamedType _ Nothing ct))   = getTI ct
getETI (ETMandatory (NamedType _ (Just t) ct))  = t
getETI (ETExtMand (NamedType _ Nothing ct))     = getTI ct
getETI (ETExtMand (NamedType _ (Just t) ct))    = t
getETI (ETOptional (NamedType _ Nothing ct))   = getTI ct
getETI (ETOptional (NamedType _ (Just t) ct))  = t
getETI (ETDefault (NamedType _ Nothing ct) d)  = getTI ct
getETI (ETDefault (NamedType _ (Just t) ct) d) = t

getTI :: ASNType a -> TagInfo
getTI (TYPEASS _ (Just tg) _)   = tg
getTI (TYPEASS _ _ t)           = getTI t
getTI BOOLEAN                   = (Universal, 1, Explicit)
getTI INTEGER                   = (Universal,2, Explicit)
getTI (RANGE c _ _)             = getTI c
getTI IA5STRING                 = (Universal,22, Explicit)
getTI BITSTRING                 = (Universal, 3, Explicit)
getTI PRINTABLESTRING           = (Universal, 19, Explicit)
getTI VISIBLESTRING             = (Universal, 26, Explicit)
getTI NUMERICSTRING             = (Universal, 18, Explicit)
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

-- 27. Encoding the restricted character string types (NUMERICSTRING)

encodeNS :: ConstrainedType NumericString -> NumericString -> BitStream
encodeNS = manageSize encodeNumSz encodeNum

encodeNumSz :: ConstrainedType NumericString -> Integer -> Integer -> NumericString -> BitStream
encodeNumSz t@(SIZE ty _ _) l u x@(NumericString xs)
    = manageExtremes encNS (encodeNum ty . NumericString) l u xs

encodeNum :: ConstrainedType NumericString -> NumericString -> BitStream
encodeNum ns (NumericString s)
    = encodeInsert insertLNS ns s

insertLNS :: ConstrainedType NumericString -> [[String]] -> [BitStream]
insertLNS s = unfoldr (nsLengths s)


-- vsLengths adds lengths values to encoding of sections of
-- VISIBLESTRING.

nsLengths :: ConstrainedType NumericString -> [[String]] -> Maybe (BitStream, [[String]])
nsLengths s = ulWrapper encNS (++) arg1 ld2

encNC c  = minBits ((toInteger . (posInStr 0 " 0123456789")) c, 10)
encNS s  = (concat . map encNC) s

posInStr n (a:r) c
    = if a == c then n else posInStr (n+1) r c
posIntStr n [] c
    = error "Not in string"

-- Decoding

n16k = 16*(2^10)

mmGetBit :: (MonadState (B.ByteString,Int64) m, MonadError String m) => m Word8
mmGetBit =
   do (ys,x) <- get
      y <- mGetBit x ys
      put (ys,x+1)
      return y

mGetBit o xs =
   if B.null ys
      then throwError ("Unable to decode " ++ show xs ++ " at bit " ++ show o)
      else return u
   where (nBytes,nBits) = o `divMod` 8
         ys = B.drop nBytes xs
         z = B.head ys
         u = (z .&. ((2^(7 - nBits)))) `shiftR` (fromIntegral (7 - nBits))

mmGetBits :: (MonadState (B.ByteString,Int64) m, MonadError String m, Integral n) => n -> m [Word8]
mmGetBits n =
   sequence (genericTake n (repeat mmGetBit))
   

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

mmDecodeWithLengthDeterminant k =
   do p <- mmGetBit
      case p of
         -- 10.9.3.6
         0 ->
            do j <- mmGetBits 7
               let l = fromNonNeg j
               mmGetBits (l*k)
         1 ->
            do q <- mmGetBit 
               case q of
                  -- 10.9.3.7
                  0 ->
                     do j <- mmGetBits 14
                        let l = fromNonNeg j
                        mmGetBits (l*k)
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           -- For now - we should handle error positions generically inside the monad
                           then throwError ("Unable to decode with fragment size of " ++ show fragSize)
                           else do frag <- mmGetBits (fragSize*n16k*k)
                                   -- This looks like it might be quadratic in efficiency!
                                   rest <- mmDecodeWithLengthDeterminant k
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

mmUntoPerInt t =
   case p of
      -- 10.5 Encoding of a constrained whole number
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1
             n     = genericLength (minBits ((ub-lb),range-1)) in
            if range <= 1
               -- 10.5.4
               then return lb
               -- 10.5.6 and 10.3 Encoding as a non-negative-binary-integer
               else do j <- mmGetBits n
                       return (lb + (fromNonNeg j))
      -- 12.2.3, 10.7 Encoding of a semi-constrained whole number,
      -- 10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
      Constrained (Just lb) Nothing ->
         do o <- mmDecodeWithLengthDeterminant 8
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

mmFromPerSeq :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => BitStream -> Sequence a -> m a
mmFromPerSeq _ Nil = return Empty
mmFromPerSeq bitmap (Cons t ts) =
   do x <- mFromPer t
      xs <- mmFromPerSeq bitmap ts
      return (x:*:xs)
mmFromPerSeq bitmap (Optional t ts) =
   -- The bitmap always matches the Sequence but we recurse the Sequence twice so this needs to be fixed
   do if (head bitmap) == 0
         then
            do xs <- mmFromPerSeq (tail bitmap) ts
               return (Nothing:*:xs)
         else
            do x <- mFromPer t
               xs <- mmFromPerSeq (tail bitmap) ts
               return ((Just x):*:xs)

mmFromPerSeqAux :: [Bool] -> Sequence a -> [Bool]
mmFromPerSeqAux preamble Nil = preamble
mmFromPerSeqAux preamble (Cons t ts) = mmFromPerSeqAux preamble ts
mmFromPerSeqAux preamble (Optional t ts) = True:(mmFromPerSeqAux preamble ts)

{-
xxx :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => m Integer
xxx = mFromPer INTEGER

mFoo :: (MonadState (B.ByteString, Int64) m, MonadError [Char] m) => m (Integer:*:Nil)
mFoo = liftM2 (:*:) (mFromPer INTEGER) (mmFromPerSeq Nil)

mmmFromPerSeq :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => Sequence a -> m a
mmmFromPerSeq Nil = return Empty
mmmFromPerSeq (Cons t ts) =
   liftM2 (:*:) (mFromPer t) (mmFromPerSeq ts)
-}

fromPer :: (MonadState Int64 m, MonadError [Char] m) => ConstrainedType a -> B.ByteString -> m a
fromPer t@INTEGER x                 = mUntoPerInt t x
fromPer r@(RANGE INTEGER l u) x     = mUntoPerInt r x
fromPer (SEQUENCE s) x              = mFromPerSeq s x

mFromPer :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => ConstrainedType a -> m a
mFromPer t@INTEGER                 = mmUntoPerInt t
mFromPer r@(RANGE INTEGER l u)     = mmUntoPerInt r
mFromPer (SEQUENCE s)              = 
   do let bitmap = mmFromPerSeqAux [] s
      ps <- mmGetBits (genericLength bitmap)
      -- fromIntegral for now until we sort out why there's a Word8 / Int clash
      mmFromPerSeq (map fromIntegral ps) s

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
t1 = RANGE INTEGER (Just 25) (Just 30)
t2 = INCLUDES INTEGER t1
t3 = INCLUDES t1 t1
t4 = RANGE INTEGER (Just (-256)) Nothing
t41 = RANGE INTEGER (Just 0) (Just 18000)
t42 = RANGE INTEGER (Just 3) (Just 3)
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
integer2 = toPer (RANGE INTEGER Nothing (Just 65535)) 127
tInteger2 = RANGE INTEGER Nothing (Just 65535)
vInteger2 = 127
integer3 = toPer (RANGE INTEGER Nothing (Just 65535)) (-128)
integer4 = toPer (RANGE INTEGER Nothing (Just 65535)) 128


-- Semi-constrained INTEGER

tInteger5 = RANGE INTEGER (Just (-1)) Nothing
vInteger5 = 4096
integer5  = toPer (RANGE INTEGER (Just (-1)) Nothing) 4096
tInteger6 = RANGE INTEGER (Just 1) Nothing
vInteger6 = 127
integer6  = toPer (RANGE INTEGER (Just 1) Nothing) 127
tInteger7 = RANGE INTEGER (Just 0) Nothing
vInteger7 = 128
integer7  = toPer (RANGE INTEGER (Just 0) Nothing) 128

-- Constrained INTEGER

integer8'1 = toPer (RANGE INTEGER (Just 3) (Just 6)) 3
integer8'2 = toPer (RANGE INTEGER (Just 3) (Just 6)) 4
integer8'3 = toPer (RANGE INTEGER (Just 3) (Just 6)) 5
integer8'4 = toPer (RANGE INTEGER (Just 3) (Just 6)) 6
integer9'1 = toPer (RANGE INTEGER (Just 4000) (Just 4254)) 4002
integer9'2 = toPer (RANGE INTEGER (Just 4000) (Just 4254)) 4006
integer10'1 = toPer (RANGE INTEGER (Just 4000) (Just 4255)) 4002
integer10'2 = toPer (RANGE INTEGER (Just 4000) (Just 4255)) 4006
integer11'1 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 0
integer11'2 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 31000
integer11'3 = toPer (RANGE INTEGER (Just 0) (Just 32000)) 32000
integer12'1 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 1
integer12'2 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 257
integer12'3 = toPer (RANGE INTEGER (Just 1) (Just 65538)) 65538



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


-- X691: A.4.1 Example Includes extensible type with extension addition groups.

ax
    = TYPEASS "Ax" Nothing
        (SEQUENCE
            (Cons (NAMEDTYPE "a" Nothing (RANGE INTEGER (Just 250) (Just 253)))
                (Cons (NAMEDTYPE "b" Nothing BOOLEAN)
                    (Cons EXTENSIBLE
                        (ConsA (EXTADDGROUP
                                 (Cons (NAMEDTYPE "g" Nothing (SIZE NUMERICSTRING (Just 3) (Just 3)))
                                             (Optional (NAMEDTYPE "h" Nothing BOOLEAN) Nil)))
                            (Cons EXTENSIBLE
                                (Optional (NAMEDTYPE "i" Nothing VISIBLESTRING)
                                    (Optional (NAMEDTYPE "j" Nothing VISIBLESTRING) Nil))))))))


axVal
    = (253 :*: (True :*: (Extensible :*:((Just (NumericString "123" :*:(Just True :*: Empty)))
            :*: (Extensible :*: (Nothing :*: (Nothing :*: Empty)))))))

axEx = toPer ax axVal

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
-- ** uncompTest1 = runState (runErrorT (untoPerInt (RANGE INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0
mUncompTest1 = runState (runErrorT (mUntoPerInt (RANGE INTEGER (Just 3) (Just 6)) (B.pack [0xc0,0,0,0]))) 0

-- These tests are wrong
-- uncompTest2 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x18,0,1,1]))) 0
-- uncompTest3 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x81,0x80,0,0]))) 0


-- Tests for semi-constrained INTEGERs
-- We need to replace decodeLengthDeterminant with untoPerInt
-- ** unInteger5 = runState (runErrorT (decodeLengthDeterminant (B.pack [0x02,0x10,0x01]))) 0
mUnInteger5 = runState (runErrorT (mUntoPerInt (RANGE INTEGER (Just (-1)) Nothing) (B.pack [0x02,0x10,0x01]))) 0


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

natural = RANGE INTEGER (Just 0) Nothing

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

mmIdem :: ConstrainedType a -> BitStream -> a
mmIdem t x =
   case runTest x 0 of
      (Left _,_)   -> undefined
      (Right xs,_) -> xs
   where
      runTest x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

testType3 = SEQUENCE (Optional t1 (Optional t1 Nil))
testVal3  = (Just 29):*:((Just 30):*:Empty)
testToPer3 = toPer testType3 testVal3
testFromPer3 = mmIdem testType3 testToPer3

seq1 = SEQUENCE (Cons t1 (Cons t1 Nil))

seqTest1 =
   case d of
      (Left x,(u,v))   -> show x
      (Right x,(u,v)) -> show x

d = runState (runErrorT (mFromPer seq1)) (B.pack [0xb4],0)

seq2 = SEQUENCE (Optional t1 (Optional t1 Nil))

seqTest :: Show a => ConstrainedType a -> [Word8] -> String
seqTest t xs =
   case d of
      (Left x,(u,v))   -> show x
      (Right x,(u,v)) -> show x
   where d = runState (runErrorT (mFromPer t)) (B.pack xs,0)


foo =
   do h <- openFile "test" ReadMode
      b <- B.hGetContents h
      let d =  runState (runErrorT (mUntoPerInt (RANGE  INTEGER (Just 25) (Just 30)) b)) 0
      case d of
         (Left e,s)  -> return (e ++ " " ++ show s)
         (Right n,s) -> return (show n ++ " " ++ show s)
