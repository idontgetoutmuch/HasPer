\documentclass{article}
%include polycode.fmt

\begin{document}

\section{Introduction}

The encoding is for UNALIGNED PER

\begin{code}
module ConstrainedType where

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
\end{code}

Some type aliases and newtype declarations

\begin{code}
type BitStream = [Int]

newtype IA5String = IA5String {iA5String :: String}

instance Show IA5String where
   show s = iA5String s

newtype BitString = BitString {bitString :: BitStream}
   deriving Show

newtype PrintableString = PrintableString {printableString :: String}
newtype NumericString = NumericString {numericString :: String}

instance Show NumericString where
   show s = numericString s

instance Show PrintableString where
   show s = printableString s
\end{code}

X.680 (07/2002) Section 47.1 Table 9

\begin{code}
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
\end{code}

Heterogeneous lists and GADTs for Sequence / Choice

\begin{code}
data Nil = Empty
data a:*:l = a:*:l
\end{code}

A sequence is a collection of element types

\begin{code}
data Sequence :: * -> * where
   Nil     :: Sequence Nil
   Extens  :: Sequence l    -> Sequence l
   Cons    :: ElementType a -> Sequence l -> Sequence (a:*:l)
\end{code}

An element type is either mandatory, optional, or default.
The second constructor ETExtMand deals with an extension
addition which is neither optional nor default.

\begin{code}

data ElementType :: * -> * where
   ETMandatory :: NamedType a -> ElementType a
   ETExtMand   :: NamedType a -> ElementType (Maybe a)
   ETOptional  :: NamedType a -> ElementType (Maybe a)
   ETDefault   :: NamedType a -> a -> ElementType (Maybe a)

\end{code}

A named type associates a type with a name and (possibly)
a tag.

\begin{code}

data NamedType :: * -> * where
   NamedType :: Name -> Maybe TagInfo -> ASNType a -> NamedType a

\end{code}

A choice is a collection of named types. The Choice type
is similar to a Sequence except that each value
is optional and only one value can exist at a time. Note
that the Choice type has no PER-visible constraints.
The constructors ChoiceExt and ChoiceEAG deal with
extension markers and extension addition groups respectively.

\begin{code}

data Choice :: * -> * where
    NoChoice     :: Choice Nil
    ChoiceExt    :: Choice l -> Choice l
    ChoiceEAG    :: Choice l -> Choice l
    ChoiceOption :: NamedType a -> Choice l -> Choice ((Maybe a):*:l)

\end{code}

An enumeration is a collection of identifiers (implicitly or explicitly) associated
with an integer.

\begin{code}

data EnumerationItem :: * -> * where
    Identifier :: Name -> EnumerationItem Name
    NamedNumber :: Name -> Integer -> EnumerationItem Name

data Enumerate :: * -> * where
    NoEnum      :: Enumerate Nil
    EnumOption  :: EnumerationItem a -> Enumerate l -> Enumerate ((Maybe a):*:l)
    EnumExt     :: Enumerate l -> Enumerate l

\end{code}

Type Aliases for Tag Information

\begin{code}

type TagInfo    = (TagType, TagValue, TagPlicity)
type TypeRef    = String
type Name       = String

\end{code}

ASNType

\begin{code}

data ASNType :: * -> * where
   TYPEASS         :: TypeRef -> Maybe TagInfo -> ASNType a -> ASNType a
   EXTADDGROUP     :: Sequence a -> ASNType a
   BOOLEAN         :: ASNType Bool
   INTEGER         :: ASNType Integer
   ENUMERATED      :: Enumerate a -> ASNType a
   BITSTRING       :: ASNType BitString
   PRINTABLESTRING :: ASNType PrintableString
   IA5STRING       :: ASNType IA5String
   VISIBLESTRING   :: ASNType VisibleString
   NUMERICSTRING   :: ASNType NumericString
   SINGLE          :: SingleValue a => ASNType a -> a -> ASNType a
   INCLUDES        :: ContainedSubtype a => ASNType a -> ASNType a -> ASNType a
   RANGE           :: ASNType Integer -> Maybe Integer -> Maybe Integer -> ASNType Integer
   SEQUENCE        :: Sequence a -> ASNType a
   SEQUENCEOF      :: ASNType a -> ASNType [a]
   SIZE            :: ASNType a -> Lower -> Upper -> ASNType a
-- REMOVED SizeConstraint a => from above
   SET             :: Sequence a -> ASNType a
   SETOF           :: ASNType a -> ASNType [a]
   CHOICE          :: Choice a -> ASNType a
   FROM            :: PermittedAlphabet a => ASNType a -> a -> ASNType a

\end{code}

Type aliases used when defining a size-constrained value.

\begin{code}

type Upper = Maybe Integer
type Lower = Maybe Integer

\end{code}

Type used to represent the lower and upper bounds of a range or
size-constrained value.

\begin{code}

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
\end{code}

bounds returns the range of a value. Nothing indicates
no lower or upper bound.

\begin{code}
bounds :: Ord a => ASNType a -> Constraint a
bounds (INCLUDES t1 t2)   = (bounds t1) `mappend` (bounds t2)
bounds (RANGE t l u)      = (bounds t) `mappend` (Constrained l u)
bounds _                  = Constrained Nothing Nothing
\end{code}

sizeLimit returns the size limits of a value. Nothing
indicates no lower or upper bound.

\begin{code}

sizeLimit :: ASNType a -> Constraint Integer
sizeLimit (SIZE t l u) = sizeLimit t `mappend` Constrained l u
sizeLimit _            = Constrained Nothing Nothing

\end{code}

manageSize is a HOF used to manage the three size cases for a
type amenable to a size constraint.

\begin{code}

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

\end{code}

toPer is the top-level PER encoding function. It currently uses
the function toPer8s to apply the relevant `multiple-of-8'
padding.
This will be replaced with toPer functions that keep a running
counter.

\begin{code}

toPer :: ASNType a -> a -> [Int]
toPer (TYPEASS tr tg ct) v                      = toPer8s ct v
toPer (EXTADDGROUP s) x                         = toPerOpen (SEQUENCE s) x
toPer t@BOOLEAN x                               = encodeBool t x
toPer t@INTEGER x                               = encodeInt t x
toPer r@(RANGE i l u) x                         = encodeInt r x
toPer (ENUMERATED e) x                          = encodeEnum e x
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

toPer8s ct v
    = let bts = toPer ct v
          lbs = genericLength bts
          rb  = lbs `mod` 8
        in
            if rb == 0
                then bts
            else
               bts ++ take (8-rb) (repeat 0)

\end{code}


maxB and minB are used when one has a nested size-constrained
value.

\begin{code}

maxB Nothing (Just b)  = Just b
maxB (Just b) Nothing  = Just b
maxB (Just a) (Just b) = Just (max a b)
maxB _ _               = Nothing

minB Nothing (Just b)  = Just b
minB (Just b) Nothing  = Just b
minB (Just a) (Just b) = Just (min a b)
minB _ _               = Nothing

\end{code}

toPerOpen encodes an open type value. That is:
i. the value is encoded as ususal;
ii. it is padded at the end with 0s so that it has a octet-multiple length; and
iii. its length is added as a prefix using the fragmentation rules (10.9)
The first case is required since an extension addition group is
encoded as an open type sequence and toPerOpen is always called by
toPer on an extension component (avoids encoding it as an open
type open type sequence!)

\begin{code}

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

\end{code}

11 ENCODING THE BOOLEAN TYPE

\begin{code}

encodeBool :: ASNType Bool -> Bool -> BitStream
encodeBool t True = [1]
encodeBool t _    = [0]

\end{code}

10.3 -- 10.8 ENCODING THE INTEGER TYPE

\begin{code}

encodeInt :: ASNType Integer -> Integer -> BitStream
encodeInt t x =
   case p of
\end{code}
       10.5 Encoding of a constrained whole number
\begin{code}
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1 in
            if range <= 1
\end{code}
                10.5.4
\begin{code}
               then []
\end{code}
                10.5.6 and 10.3 Encoding as a non-negative-binary-integer
\begin{code}
               else encodeNNBIntBits ((x-lb),range-1)
\end{code}
       12.2.3, 10.7 Encoding of a semi-constrained whole number,
       10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
\begin{code}
      Constrained (Just lb) Nothing ->
                encodeSCInt x lb
\end{code}
       12.2.4, 10.8 Encoding of an unconstrained whole number, 10.8.3 and
       10.4 Encoding as a 2's-complement-binary-integer
\begin{code}
      Constrained Nothing _ ->
                encodeUInt x
   where
      p = bounds t

\end{code}

 10.6 Encoding as a normally small non-negative whole number

\begin{code}

encodeNSNNInt :: Integer -> Integer -> BitStream
encodeNSNNInt n lb
    = if n <= 63
        then 0:encodeNNBIntBits (n,63)
        else 1:encodeSCInt n lb

\end{code}


 10.3 Encoding as a non-negative-binary-integer

 encodeNNBIntBits encodes an integer in the minimum
 number of bits required for the range (assuming the range is at least 2).

\begin{code}

encodeNNBIntBits :: (Integer, Integer) -> BitStream
encodeNNBIntBits
    = reverse . (map fromInteger) . unfoldr h
      where
        h (_,0) = Nothing
        h (0,w) = Just (0, (0, w `div` 2))
        h (n,w) = Just (n `mod` 2, (n `div` 2, w `div` 2))

\end{code}

 encodeNNBIntOctets encodes an integer in the minimum number of
 octets.

\begin{code}

encodeNNBIntOctets :: Integer -> BitStream
encodeNNBIntOctets =
   reverse . (map fromInteger) . flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))

\end{code}

 10.7 Encoding of a semi-constrained whole number. The integer
 is encoded in the minimum number of octets with an explicit
 length encoding. In the larger cases there may be fragmentation
 of the number encoding.

\begin{code}

encodeSCInt :: Integer -> Integer -> BitStream
encodeSCInt v lb
    = encodeWithLengthDeterminant (encodeNNBIntOctets (v-lb))

\end{code}

 10.8 Encoding of an unconstrained integer. The integer is
 encoded as a 2's-complement-binary-integer with an explicit
 length encoding. In the larger cases there may be fragmentation
 of the number encoding.

\begin{code}

encodeUInt :: Integer -> BitStream
encodeUInt x = encodeWithLengthDeterminant (to2sComplement x)

\end{code}

10.9 General rules for encoding a length determinant
10.9.4, 10.9.4.2 and 10.9.3.4 to 10.9.3.8.4.

encodeInsert is a HOF which manages the fragmentation and
encoding of a value with an unconstrained length.

\begin{code}

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

\end{code}

HOFs of use when encoding values with an unconstrained length
where the length value has to be interspersed with value encoding.

\begin{code}
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
arg1 x y = (1:1:(encodeNNBIntBits (x,y)))

\end{code}

addLengths adds length encoding to a sectioned bitstream. Note
that the input bits are unchanged as the first argument to ulWrapper is the
identity function.

\begin{code}

addLengths :: [[[BitStream]]] -> Maybe ([BitStream], [[[BitStream]]])
addLengths = ulWrapper id (:) arg1 ld

\end{code}

\begin{enumerate}

\item
The first guard implements 10.9.4.2, 10.9.3.5, 10.9.3.6. Note this is
not very efficient since we know $log_2 128 = 7$

\item
The second guard implements 10.9.3.7. Note this is
not very efficient since we know $log_2 16*(2^{10}) = 14$

\item
Note there is no clause for $>= 16*(2^10)$ as we have groupBy $16*(2^10)$

\end{enumerate}

\begin{code}

ld :: Integer -> [BitStream]
ld n
   | n <= 127       = [0:(encodeNNBIntBits (n, 127))]
   | n < 16*(2^10)  = [1:0:(encodeNNBIntBits (n, (16*(2^10)-1)))]

\end{code}

\section{Two's Complement Arithmetic}

10.4 Encoding as a 2's-complement-binary-integer is used when
encoding an integer with no lower bound (10.8) as in the final
case of encodeInt. The encoding of the integer is accompanied
by the encoding of its length using encodeWithLengthDeterminant
(10.8.3)

\begin{code}

to2sComplement :: Integer -> BitStream
to2sComplement n
   | n >= 0 = 0:(h n)
   | otherwise = encodeNNBIntOctets (2^p + n)
   where
      p = length (h (-n-1)) + 1

g :: (Integer, Integer) -> Maybe (Integer, (Integer, Integer))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h :: Integer -> BitStream
h n = (reverse . map fromInteger) (flip (curry (unfoldr g)) 7 n)

\end{code}

 13 ENCODING THE ENUMERATED TYPE

There are three cases to deal with:

\begin{enumerate}

\item
There is no extension marker. The enumerations are indexed
based on their (explicit or implicit) values. Thus each
enumeration without an explcit value, is given a value that is not
already explcitly assigned (assignNumber) on a first come/first
serve basis. The indexes are then assigned in ascending
order where the first index is 0 (assignIndex). The total number of
enumerations is required since the encoding is of a constrained
integer i.e. in the minimum number of bits. (13.2 and 10.5.6)
encodeEnumAux simply encodes the existing enumeration.

\item

There is an extension marker but the value is in the
enumeration root. 0 prefixes the encoding of the value
which is completed as in (i). assignIndex returns a
Boolean which indicates the presence or absence of an extension
marker. (13.3 and 10.5.6)

\item
The value is in the extension. 1 prefixes the encoding,
the enumerations in the extension are indexed in order of
appearance and are encoded as a normally small non-negative whole
number. (13.3 and 10.6) The function encodeEnumExtAux manages this
encoding.

\end{enumerate}

\begin{code}

encodeEnum :: Enumerate a -> a -> BitStream
encodeEnum e x
    = let (b,inds) = assignIndex e
          no = genericLength inds
      in encodeEnumAux b no inds e x

encodeEnumAux :: Bool -> Integer -> [Integer] -> Enumerate a -> a -> BitStream
encodeEnumAux b no (f:r) (EnumOption _ es) (Just n :*:rest)
    = if not b
        then encodeNNBIntBits (f, no-1)
        else 0: encodeNNBIntBits (f, no-1)
encodeEnumAux b no (f:r) (EnumOption _ es) (Nothing :*: rest)
    = encodeEnumAux b no r es rest
encodeEnumAux b no inds (EnumExt ex) x
    = let el = noEnums ex
      in encodeEnumExtAux 0 el ex x
encodeEnumAux _ _ _ _ _ = error "No enumerated value!"

encodeEnumExtAux :: Integer -> Integer -> Enumerate a -> a -> BitStream
encodeEnumExtAux i l (EnumOption _ es) (Just n :*:rest)
    = 1:encodeNSNNInt i 0
encodeEnumExtAux i l (EnumOption _ es) (Nothing :*:rest)
    = encodeEnumExtAux (i+1) l es rest
encodeEnumExtAux i l _ _ = error "No enumerated extension value!"

assignIndex :: Enumerate a -> (Bool, [Integer])
assignIndex en
    = let (b,ns) = assignNumber en False []
          sls = sort ns
      in
        (b, positions ns sls)

assignNumber :: Enumerate a -> Bool -> [Integer] -> (Bool, [Integer])
assignNumber en b ls
    = let nn = getNamedNumbers en
      in
        assignN ([0..] \\ nn) en b ls

assignN :: [Integer] -> Enumerate a -> Bool -> [Integer] -> (Bool, [Integer])
assignN (f:xs) NoEnum b ls = (b,reverse ls)
assignN (f:xs) (EnumOption (NamedNumber _ i) r)b ls = assignN (f:xs) r b (i:ls)
assignN (f:xs) (EnumOption _ r) b ls = assignN xs r b (f:ls)
assignN (f:xs) (EnumExt r) b ls = (True, reverse ls)


getNamedNumbers :: Enumerate a -> [Integer]
getNamedNumbers NoEnum = []
getNamedNumbers (EnumOption (NamedNumber _ i) r) = i:getNamedNumbers r
getNamedNumbers (EnumOption _ r) = getNamedNumbers r
getNamedNumbers (EnumExt r)  = []

noEnums :: Enumerate a -> Integer
noEnums NoEnum = 0
noEnums (EnumOption _ r) = 1 + noEnums r
noEnums (EnumExt r)  = 0

positions [] sls = []
positions (f:r) sls
    = findN f sls : positions r sls

findN i (f:r)
    = if i == f then 0
        else 1 + findN i r
findN i []
    = error "Impossible case!"

\end{code}


\section{ENCODING THE BITSTRING TYPE}


\begin{code}

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

\end{code}


\begin{code}
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
\end{code}

18 ENCODING THE SEQUENCE TYPE

\begin{code}

encodeSeq :: Sequence a -> a -> BitStream
encodeSeq s x
    =   let ((rp,rb),(ap,ab)) = encodeSeqAux ([],[]) ([],[]) s x
        in  if null ap
          then
             concat rp ++ concat rb ++ concat ap ++ concat ab
          else
             concat rp ++ concat rb ++ lengthAdds ap ++ concat ab

\end{code}

I DON'T THINK THAT THE ELSE CASE IS FRAGMENTING CORRECTLY

18.8 A length determinant of the number of extension additions is added if
the sequence has any extension additions declared. This is encoded as a normally
small length (10.9.3.4)

\begin{code}

lengthAdds ap
    = let la = genericLength ap
       in if la <= 63
        then 0:encodeNNBIntBits (la-1, 63) ++ concat ap
        else 1:encodeWithLengthDeterminant (encodeNNBIntOctets la) ++ concat ap

\end{code}

encodeSeqAux is the auxillary function for encodeSeq. When
encoding a sequence, one has to both encode each component and
produce a preamble which indicates the presence or absence of an
optional or default value. The first list in the result is the
preamble. The constructor Extens indicates the sequence is
extensible, and the coding responsibility is passed to
encodeExtSeqAux (where the values are encoded as an open type).
Note that if another Extens occurs then reponsibility returns
to encodeSeqAux since this is the 2 extension marker case
(and what follows is in the extension root).

\begin{code}

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

\end{code}

encodeExtSeqAux adds the encoding of any extension additions to
the encoding of the extension root. If an addition is present a
1 is added to a bitstream prefix and the value is encoded as an
open type (using toPerOpen). If an addition is not present then a
0 is added to the prefix.

\begin{code}

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

\end{code}


19. ENCODING THE SEQUENCE-OF TYPE

encodeSO implements the encoding of an unconstrained
sequence-of value. This requires both the encoding of
each of the components, and in most cases the encoding
of the length of the sequence of (which may require
fragmentation into 64K blocks). It uses the function manageSize
which manages the 3 possible size cases.

\begin{code}

encodeSO :: ASNType [a] -> [a] -> BitStream
encodeSO  = manageSize encodeSeqSz encodeSeqOf

\end{code}

encodeSeqSz encodes a size-constrained SEQUENCEOF. It uses the
function manageExtremes which manages the 3 upper/lower bound size value cases.

\begin{code}

manageExtremes :: ([a] -> BitStream) -> ([a] -> BitStream) -> Integer -> Integer -> [a] -> BitStream
manageExtremes fn1 fn2 l u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
               then fn1 x
               else if u >= 65536
                   then fn2 x
                   else encodeNNBIntBits ((genericLength x-l),range-1) ++ fn1 x

encodeSeqSz :: ASNType [a] -> Integer -> Integer -> [a] -> BitStream
encodeSeqSz (SIZE ty _ _) l u x
        = manageExtremes (encodeNoL ty) (encodeSeqOf ty) l u x


encodeSeqOf :: ASNType a -> a -> BitStream
encodeSeqOf (SEQUENCEOF s) xs
    = encodeWithLD s xs

\end{code}

encodeWithLD splits the components into 16K blocks, and then
splits these into blocks of 4 (thus a maximum of 64K in each
block). insertL then manages the interleaving of the length-value
encoding of the components.

\begin{code}

encodeWithLD :: ASNType a -> [a] -> BitStream
encodeWithLD s
    = encodeInsert insertL s

insertL :: ASNType a -> [[[a]]] -> [BitStream]
insertL s = unfoldr (soLengths s)

\end{code}

soLengths adds length values to encodings of SEQUENCEOF
components.

\begin{code}

soLengths :: ASNType a -> [[[a]]] -> Maybe (BitStream, [[[a]]])
soLengths t = ulWrapper (concat . map (toPer t)) (++) arg1 ld2

ld2 n
   | n <= 127       = 0:(encodeNNBIntBits (n, 127))
   | n < 16*(2^10)  = 1:0:(encodeNNBIntBits (n, (16*(2^10)-1)))

\end{code}

No length encoding of SEQUENCEOF

\begin{code}

encodeNoL :: ASNType a -> a -> BitStream
encodeNoL (SEQUENCEOF s) xs
    = (concat . map (toPer s)) xs

\end{code}

20. Encoding the SET type. The encoding is the same as for a
SEQUENCE except that the components must be canonically ordered.
The ordering is based on the component's tags. Note, the
preamble must be reordered to match the ordering of the
components.

\begin{code}

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

\end{code}


Sorting

\begin{code}

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

\end{code}

 Sorting predicate and tag selector

\begin{code}

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

\end{code}


 21. Encoding the set-of type.

 Since we are implementing BASIC-PER (and not CANONICAL-PER) the
 encoding is as for a sequence-of.


 22. Encoding the choice type.

encodeChoice encodes CHOICE values. It is not dissimilar to
encodeSet in that the possible choice components must be
assigned an index based on their canonical ordering. This index,
which starts from 0, prefixes the value encoding and is absent if
there is only a single choice. The auxillary function
encodeChoiceAux deals with the possible cases, and
encodeChoiceAux' is called once a value has been encoded to ensure
that only one choice value is encoded.

\begin{code}

encodeChoice :: Choice a -> a -> BitStream
encodeChoice c x
    =   let ts  = getCTags c
            (ea, ec)  = (encodeChoiceAux [] [] c x)
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
            if null ea
              then encodeNNBIntBits (fst fr,ls-1) ++ (snd .snd) fr
                    else
                if length ec <= 63
                    then ea ++ 0:encodeNNBIntBits (fst fr, 63) ++ (snd.snd) fr
                    else ea ++ 1:encodeWithLengthDeterminant (encodeNNBIntOctets (fst fr)) ++ (snd.snd) fr

\end{code}

 IS THE ELSE CASE ABOVE CORRECT???

\begin{code}

nullValue :: (Integer, (TagInfo, BitStream)) -> Bool
nullValue (f,(s,t)) = null t

getCTags :: Choice a -> [TagInfo]
getCTags NoChoice                     = []
getCTags (ChoiceExt xs)               = getCTags xs
getCTags (ChoiceEAG xs)               = getCTags xs
getCTags (ChoiceOption (NamedType n t (EXTADDGROUP (Cons v rs))) xs)
        = getETI v : getCTags (ChoiceOption (NamedType n t (EXTADDGROUP rs))xs)
getCTags (ChoiceOption (NamedType n t (EXTADDGROUP Nil)) xs)
        = getCTags xs
getCTags (ChoiceOption (NamedType n Nothing a) xs)
        = getTI a : getCTags xs
getCTags (ChoiceOption (NamedType n (Just t) a) xs)
        = t : getCTags xs

choicePred :: (TagInfo, BitStream) -> (TagInfo, BitStream) -> Bool
choicePred (t1,_) (t2,_) = t1 < t2


encodeChoiceAux :: [Int] -> [BitStream] -> Choice a -> a -> ([Int], [BitStream])
encodeChoiceAux ext body NoChoice _ = (ext, reverse body)
encodeChoiceAux ext body (ChoiceExt as) xs =
   encodeChoiceExtAux [0] body as xs
encodeChoiceAux ext body (ChoiceOption a as) (Nothing:*:xs) =
   encodeChoiceAux ext ([]:body) as xs
encodeChoiceAux ext body (ChoiceOption (NamedType n t a) as) ((Just x):*:xs) =
   encodeChoiceAux' ext ((toPer a x):body) as xs


encodeChoiceAux' :: [Int] -> [BitStream] -> Choice a -> a -> ([Int], [BitStream])
encodeChoiceAux' ext body NoChoice _ = (ext, reverse body)
encodeChoiceAux' ext body (ChoiceExt as) xs =
   encodeChoiceExtAux' ext body as xs
encodeChoiceAux' ext body (ChoiceOption a as) (x:*:xs) =
   encodeChoiceAux' ext ([]:body) as xs

encodeChoiceExtAux :: [Int] -> [BitStream] -> Choice a -> a -> ([Int], [BitStream])
encodeChoiceExtAux ext body NoChoice _ = (ext,reverse body)
encodeChoiceExtAux ext body (ChoiceExt as) xs =
   encodeChoiceAux ext body as xs
encodeChoiceExtAux ext body (ChoiceEAG as) xs =
   encodeChoiceExtAux ext body as xs
encodeChoiceExtAux ext body (ChoiceOption a as) (Nothing:*:xs) =
   encodeChoiceExtAux ext ([]:body) as xs
encodeChoiceExtAux ext body (ChoiceOption (NamedType n t a) as) ((Just x):*:xs) =
   encodeChoiceExtAux' [1]((toPerOpen a x):body) as xs

encodeChoiceExtAux' :: [Int] -> [BitStream] -> Choice a -> a -> ([Int], [BitStream])
encodeChoiceExtAux' ext body NoChoice _ = (ext, reverse body)
encodeChoiceExtAux' ext body (ChoiceExt as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceEAG as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceOption a as) (x:*:xs) =
   encodeChoiceExtAux' ext body as xs

\end{code}

 27. Encoding the restricted character string types (VISIBLESTRING)

\begin{code}
encodeVS :: ASNType VisibleString -> VisibleString -> BitStream
encodeVS = manageSize encodeVisSz encodeVis

encodeVisSz :: ASNType VisibleString -> Integer -> Integer -> VisibleString -> BitStream
encodeVisSz t@(SIZE ty _ _) l u x@(VisibleString xs)
    = manageExtremes encS (encodeVis ty . VisibleString) l u xs

encodeVis :: ASNType VisibleString -> VisibleString -> BitStream
encodeVis vs (VisibleString s)
    = encodeInsert insertLVS vs s

insertLVS :: ASNType VisibleString -> [[String]] -> [BitStream]
insertLVS s = unfoldr (vsLengths s)

\end{code}

 vsLengths adds lengths values to encoding of sections of
 VISIBLESTRING.

\begin{code}

vsLengths :: ASNType VisibleString -> [[String]] -> Maybe (BitStream, [[String]])
vsLengths s = ulWrapper encS (++) arg1 ld2

encC c  = encodeNNBIntBits ((toInteger . ord) c, 94)
encS s  = (concat . map encC) s

\end{code}

 27.5.4 Encoding of a VISIBLESTRING with a permitted alphabet
 constraint.

\begin{code}

encodeVSF :: ASNType VisibleString -> VisibleString -> BitStream
encodeVSF = manageSize encodeVisSzF encodeVisF

encodeVisSzF :: ASNType VisibleString -> Integer -> Integer -> VisibleString -> BitStream
encodeVisSzF t@(SIZE ty@(FROM cv pac)_ _) l u x@(VisibleString xs)
    = manageExtremes (encSF pac) (encodeVisF ty . VisibleString) l u xs

encodeVisF :: ASNType VisibleString -> VisibleString -> BitStream
encodeVisF vs@(FROM cv pac) (VisibleString s)
    = encodeInsert (insertLVSF pac) vs s

insertLVSF :: VisibleString -> t -> [[String]] -> [BitStream]
insertLVSF p s = unfoldr (vsLengthsF s p)

\end{code}

vsLengths adds lengths values to encoding of sections of
VISIBLESTRING.

\begin{code}

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

\end{code}

Clause 38.8 in X680 (Canonical ordering of VisibleString characters)

\begin{code}

canEnc b sp [] = []
canEnc b sp (f:r)
        = let v = (toInteger . length . findV f) sp
           in encodeNNBIntBits (v,b) : canEnc b sp r

findV m []  = []
findV m (a:rs)
          = if m == a
                then []
                else a : findV m rs

\end{code}

 27. Encoding the restricted character string types (NUMERICSTRING)

\begin{code}

encodeNS :: ASNType NumericString -> NumericString -> BitStream
encodeNS = manageSize encodeNumSz encodeNum

encodeNumSz :: ASNType NumericString -> Integer -> Integer -> NumericString -> BitStream
encodeNumSz t@(SIZE ty _ _) l u x@(NumericString xs)
    = manageExtremes encNS (encodeNum ty . NumericString) l u xs

encodeNum :: ASNType NumericString -> NumericString -> BitStream
encodeNum ns (NumericString s)
    = encodeInsert insertLNS ns s

insertLNS :: ASNType NumericString -> [[String]] -> [BitStream]
insertLNS s = unfoldr (nsLengths s)

\end{code}

 vsLengths adds lengths values to encoding of sections of
 VISIBLESTRING.

\begin{code}

nsLengths :: ASNType NumericString -> [[String]] -> Maybe (BitStream, [[String]])
nsLengths s = ulWrapper encNS (++) arg1 ld2

encNC c  = encodeNNBIntBits ((toInteger . (posInStr 0 " 0123456789")) c, 10)
encNS s  = (concat . map encNC) s

posInStr n (a:r) c
    = if a == c then n else posInStr (n+1) r c
posIntStr n [] c
    = error "Not in string"

\end{code}

\section{Decoding}


\begin{code}

n16k = 16*(2^10)
n64k = 64*(2^10)

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

\end{code}

\begin{enumerate}
\item
         -- 10.9.3.6
\item
                  -- 10.9.3.7
\item
                           -- For now - we should handle error positions generically inside the monad

\item
                                   -- This looks like it might be quadratic in efficiency!
\end{enumerate}

\begin{code}

mmDecodeWithLengthDeterminant k =
   do p <- mmGetBit
      case p of
         0 ->
            do j <- mmGetBits 7
               let l = fromNonNeg j
               mmGetBits (l*k)
         1 ->
            do q <- mmGetBit
               case q of
                  0 ->
                     do j <- mmGetBits 14
                        let l = fromNonNeg j
                        mmGetBits (l*k)
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError ("Unable to decode with fragment size of " ++ show fragSize)
                           else do frag <- mmGetBits (fragSize*n16k*k)
                                   rest <- mmDecodeWithLengthDeterminant k
                                   return (frag ++ rest)

\end{code}


decodeSized only ever gets called with either no upper bound or an upper bound of $>= 64$.

It is an error if the length determinant is specified as indefinite for the first block.
We don't capture this for now.

The lowest the lower bound can be is $0$. Therefore we can assume that decodeSized only
ever gets called with a constraint of the form Constraint (Just n) \_.


\begin{code}

decodeSizedSemi :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => Integer -> Integer -> m [Word8] 
decodeSizedSemi k lb =
   do p <- mmGetBit
      case p of
         0 ->
            do j <- mmGetBits 7
               let l = fromNonNeg j
               mmGetBits ((l + lb) * k)
         1 ->
            do q <- mmGetBit
               case q of
                  0 ->
                     do j <- mmGetBits 14
                        let l = fromNonNeg j
                        mmGetBits ((l + lb) * k)
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError ("Unable to decode with fragment size of " ++ show fragSize)
                           else do frag <- mmGetBits (fragSize * n16k * k)
                                   rest <- decodeSizedSemi k lb
                                   return (frag ++ rest)

decodeSizedAsSemi :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => Integer -> Integer -> m [Word8] 
decodeSizedAsSemi k lb =
   do p <- mmGetBit
      case p of
         0 ->
            throwError ("Unexpected length bits for SIZE >= 64k")
         1 ->
            do q <- mmGetBit
               case q of
                  0 ->
                     throwError ("Unexpected length bits for SIZE >= 64k")
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError ("Unable to decode with fragment size of " ++ show fragSize)
                           else do frag <- mmGetBits (fragSize * n16k * k)
                                   rest <- decodeSizedSemi k lb
                                   return (frag ++ rest)

\end{code}

\begin{enumerate}
\item
      -- 10.5 Encoding of a constrained whole number
\item
               -- 10.5.4
\item
               -- 10.5.6 and 10.3 Encoding as a non-negative-binary-integer
\item
      -- 12.2.3, 10.7 Encoding of a semi-constrained whole number,
      -- 10.3 Encoding as a non-negative-binary-integer, 12.2.6, 10.9 and 12.2.6 (b)
\item
      -- 12.2.4, 10.8 Encoding of an unconstrained whole number, 10.8.3 and
      -- 10.4 Encoding as a 2's-complement-binary-integer
\end{enumerate}

\begin{code}

mmUntoPerInt t =
   case p of
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1
             n     = genericLength (encodeNNBIntBits ((ub-lb),range-1)) in
            if range <= 1
               then return lb
               else do j <- mmGetBits n
                       return (lb + (fromNonNeg j))
      Constrained (Just lb) Nothing ->
         do o <- mmDecodeWithLengthDeterminant 8
            return (lb + (fromNonNeg o))
      Constrained Nothing _ ->
         do o <- mmDecodeWithLengthDeterminant 8
            return (from2sComplement o)
   where
      p = bounds t

\end{code}

\begin{enumerate}

\item
The first case deals with clause 15.8.

\item
The second case deals with 15.9 and 15.10 which happen to be the same for unaligned PER.

\item
The third case deals with 15.11.

This clause is hard to understand and we reproduce it here.

15.11 If 15.8-15.10 do not apply, the bitstring shall be placed in a bit-field (octet-aligned in the ALIGNED variant)
of length "n" bits and the procedures of 10.9 shall be invoked to add this bit-field (octet-aligned in the ALIGNED
variant) of "n" bits to the field-list, preceded by a length determinant equal to "n" bits as a constrained whole number if
"ub" is set and is less than 64K or as a semi-constrained whole number if "ub" is unset. "lb" is as determined above.
    NOTE – Fragmentation applies for unconstrained or large "ub" after 16K, 32K, 48K or 64K bits.

\end{enumerate}

3rd guard is 10.9.4.1 

4th guard is the second condition of 10.9.4.2. Note we haven't covered the other two conditions yet.

decodeSizedAsSemi cpvers the second condition

the 3rd pattern match for $f$ covers the 3rd condition in 10.9.4.2.

So I think we have now covered all the relevant conditions.

\begin{code}

fromPerBitString t =
   f s
   where
      s = sizeLimit t
      f (Constrained _ (Just 0)) = return []
      f (Constrained (Just lb) (Just ub))
         | lb == ub && ub <= 16 =
            mmGetBits ub
         | lb == ub && ub <= n64k =
            mmGetBits ub
         | ub <= n64k = 
            do let n = genericLength (encodeNNBIntBits (ub - lb, ub - lb))
               j <- mmGetBits n
               mmGetBits (lb + (fromNonNeg j))
         | otherwise =
            decodeSizedAsSemi 1 lb
      f (Constrained (Just lb) Nothing) =
         decodeSizedSemi 1 lb

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

\end{code}

      -- fromIntegral for now until we sort out why there's a Word8 / Int clash

      -- This is a space leak waiting to happen

\begin{code}

mFromPer :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => ASNType a -> m a
mFromPer t@INTEGER                 = mmUntoPerInt t
mFromPer r@(RANGE i l u)           = mmUntoPerInt r
mFromPer t@BITSTRING               = (liftM (BitString . map fromIntegral) . fromPerBitString) t
mFromPer (SEQUENCE s)              =
   do ps <- mmGetBits (l s)
      mmFromPerSeq (map fromIntegral ps) s
   where
      l :: Integral n => Sequence a -> n
      l Nil = 0
      l (Cons (ETMandatory _) ts) = l ts
      l (Cons (ETOptional _ ) ts) = 1+(l ts)

\end{code}

   -- The bitmap always matches the Sequence but we recurse the Sequence twice so this needs to be fixed

I'm not really sure if this is true now having thought about it

\begin{code}

mmFromPerSeq :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => BitStream -> Sequence a -> m a
mmFromPerSeq _ Nil = return Empty
mmFromPerSeq bitmap (Cons (ETMandatory (NamedType _ _ t)) ts) =
   do x <- mFromPer t
      xs <- mmFromPerSeq bitmap ts
      return (x:*:xs)
mmFromPerSeq bitmap (Cons (ETOptional (NamedType _ _ t)) ts) =
   do if (head bitmap) == 0
         then
            do xs <- mmFromPerSeq (tail bitmap) ts
               return (Nothing:*:xs)
         else
            do x <- mFromPer t
               xs <- mmFromPerSeq (tail bitmap) ts
               return ((Just x):*:xs)

\end{code}

\end{document}
