\documentclass{article}
%include polycode.fmt

\newcommand{\bottom}{\perp}

\begin{document}

\section{Introduction}

The encoding is for UNALIGNED PER

\begin{code}
module ConstrainedType where

import Data.Monoid
import Data.List hiding (groupBy)
import Data.Bits
import Data.Char
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Error
-- import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitPut as BP
import qualified Data.Binary.Strict.BitGet as BG
-- import Data.Binary.Strict.BitUtil (rightShift)
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default), NamedType, OctetString)
import Text.PrettyPrint
import System
import IO
import Data.Int
import Data.Bits
import Data.Word
import Data.Maybe
\end{code}


The GADT ASNType which represents all ASN.1 types.

\begin{code}

data ASNType :: * -> * where
   TYPEASS         :: TypeRef -> Maybe TagInfo -> ASNType a -> ASNType a
   EXTADDGROUP     :: Sequence a -> ASNType a
   BOOLEAN         :: ASNType Bool
   INTEGER         :: ASNType Integer
   ENUMERATED      :: Enumerate a -> ASNType a
   BITSTRING       :: NamedBits -> ASNType BitString
   OCTETSTRING     :: ASNType OctetString
   PRINTABLESTRING :: ASNType PrintableString
   IA5STRING       :: ASNType IA5String
   VISIBLESTRING   :: ASNType VisibleString
   NUMERICSTRING   :: ASNType NumericString
   SINGLE          :: SingleValue a => ASNType a -> a -> ASNType a
   INCLUDES        :: ContainedSubtype a => ASNType a -> ASNType a -> ASNType a
   RANGE           :: ASNType Integer -> Lower -> Upper -> ASNType Integer
   SEQUENCE        :: Sequence a -> ASNType a
   SEQUENCEOF      :: ASNType a -> ASNType [a]
   SIZE            :: ASNType a -> Constraint -> EM -> ASNType a
   SET             :: Sequence a -> ASNType a
   SETOF           :: ASNType a -> ASNType [a]
   CHOICE          :: Choice a -> ASNType (HL a (S Z))
   FROM            :: PermittedAlphabet a => ASNType a -> a -> ASNType a
\end{code}

Some newtype declarations used to define ASNType, and type aliases to make the code more readable.

\begin{code}
newtype IA5String = IA5String {iA5String :: String}
    deriving (Eq, Show)
newtype BitString = BitString {bitString :: BitStream}
    deriving (Eq, Show)
newtype OctetString = OctetString {octetString :: OctetStream}
    deriving (Eq, Show)
newtype PrintableString = PrintableString {printableString :: String}
    deriving (Eq, Show)
newtype NumericString = NumericString {numericString :: String}
    deriving (Eq, Show)

type BitStream = [Int]
type Octet = Word8
type OctetStream = [Octet]

type TagInfo    = (TagType, TagValue, TagPlicity)
type TypeRef    = String
type Name       = String
\end{code}

Type Classes which make explicit the (not necessarily PER-visible) subtypes associated with the ASN.1 types.

See X.680 (07/2002) Section 47.1 Table 9

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

instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange Integer


class PermittedAlphabet a

instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
instance PermittedAlphabet VisibleString
instance PermittedAlphabet NumericString


class SizeConstraint a

instance SizeConstraint BitString
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
instance SizeConstraint [a]
instance SizeConstraint VisibleString
instance SizeConstraint NumericString
\end{code}

Type for heterogeneous lists. This is used in defining the Sequence, Set, Choice and Enumerated
types.

\begin{code}
data Nil = Empty
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs
\end{code}

X.680 Section 24. Sequence Type

A sequence is a (possibly heterogeneous) collection of component
types. Nil is the empty sequence, Cons adds components to a
sequence and Extens signals an extension marker.

\begin{code}
data Sequence :: * -> * where
   Nil     :: Sequence Nil
   Extens  :: Sequence l    -> Sequence l
   Cons    :: ComponentType a -> Sequence l -> Sequence (a:*:l)
\end{code}

A component type is either mandatory, optional, default or indicates
that the components of another sequence are being used.
The second constructor CTExtMand deals with an extension
addition which is neither optional nor default. It returns a Maybe
value since a mandatory extension value may not be present in a
sequence value.

Each constructor (except CTCompOf) takes a named type value which
associates a name and possibly a tag with a type.

\begin{code}

data ComponentType :: * -> * where
   CTMandatory :: NamedType a -> ComponentType a
   CTExtMand   :: NamedType a -> ComponentType (Maybe a)
   CTOptional  :: NamedType a -> ComponentType (Maybe a)
   CTDefault   :: NamedType a -> a -> ComponentType (Maybe a)
   CTCompOf    :: ASNType a   -> ComponentType a

data NamedType :: * -> * where
   NamedType :: Name -> Maybe TagInfo -> ASNType a -> NamedType a

\end{code}

X.680 Section 28. Choice type

A choice is a collection of named types. The Choice type
is similar to a Sequence except that each value
is optional and only one value can exist at a time. Note
that the Choice type has no PER-visible constraints.
The constructors ChoiceExt and ChoiceEAG deal with
extension markers and extension addition groups respectively.

In order to enforce one and only one value for a choice the ASNType
constructor CHOICE returns a value of the type
ASNType (HL a (S Z)).

HL is a type for heterogeneous lists (similar
to Sequence) except that it takes a second input which indicates
the number of actual values in the list. The empty list is
represented by EmptyHL of the type HL Nil Z where Z is a type
indicating no values. The constructor ValueC takes a value
and a list with no values and adds the value to the list.
Its retuurn type is HL (a:*:l) (S Z) indicating that the list now
has one value (S for successor). Finally the constructor
NoValueC takes no value (of the appropriate type -- hence the use
of the phantom type Phantom a) and a list and returns the list
with the non-value added. In this case the number of values in the
list is not incremented.

\begin{code}

data Choice :: * -> *  where
    NoChoice     :: Choice Nil
    ChoiceExt    :: Choice l -> Choice l
    ChoiceEAG    :: Choice l -> Choice l
    ChoiceOption :: NamedType a -> Choice l -> Choice (a:*:l)

data HL :: * -> * -> * where
    EmptyHL  :: HL Nil Z
    ValueC   :: a -> HL l Z -> HL (a:*:l) (S Z)
    NoValueC :: Phantom a -> HL l n -> HL (a:*:l) n

data Z

data S n

data Phantom a = NoValue

instance Show (HL Nil n) where
   show _ = "EmptyHL"

instance (Show a, Show (HL l n)) => Show (HL (a:*:l) n) where
   show (ValueC x _ ) = show x
   show (NoValueC _ xs) = show xs

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys

instance Eq (HL Nil (S Z)) where
   _ == _ = True

instance (Eq a, Eq (HL l (S Z))) => Eq (HL (a:*:l) (S Z)) where
   ValueC   _ _ == NoValueC _ _ = False
   NoValueC _ _ == ValueC _ _   = False
   NoValueC _ xs == NoValueC _ ys = xs == ys
   ValueC x _ == ValueC y _ = x == y

\end{code}

X.680 Section 19. Enumerated type

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

X.680 Section 48.5. Size Constraint

The type Constraint represents the set of size-constraint values used in size-constrained ASN types.

\begin{code}
data Constraint
        = Elem (Integer,Integer)
            | Union (Constraint) (Constraint)
            | Intersection (Constraint) (Constraint)
            | Except (Constraint) (Constraint)

evalCons :: Constraint -> [(Integer,Integer)]
evalCons (Elem p) = [p]
evalCons (Union x y)
    = let m = evalCons x
          n = evalCons y
      in
        unionCs m n
evalCons (Intersection x y)
    = let m = evalCons x
          n = evalCons y
      in
        intersectCs m n
evalCons (Except x y)
    = let m = evalCons x
          n = evalCons y
      in
        exceptCs m n

unionCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
unionCs m n
        | subset m n   = n
        | subset n m   = m
        | distinct m n = addCs m n
        | otherwise    = combineCs m n

intersectCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
intersectCs m n
        | subset m n   = m
        | subset n m   = n
        | distinct m n = []
        | otherwise    = intCombineCs m n

exceptCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
exceptCs m n
        | subset m n   = []
        | subset n m   = excCombineCs m n
        | distinct m n = m
        | otherwise    = excCombineCs m n

subset :: [(Integer,Integer)] -> [(Integer,Integer)] -> Bool
subset [x] [y] = isIn x y
subset p@[(a,b)] ((c,d):ys)
    = if a > d then subset p ys
               else isIn (a,b) (c,d)
subset (x:xs) p
    = subset [x] p && subset xs p

isIn :: (Integer,Integer) -> (Integer,Integer) -> Bool
isIn (a,b) (c,d) = a >= c && b <= d

distinct :: [(Integer,Integer)] -> [(Integer,Integer)] -> Bool
distinct [(a,b)] [(c,d)] = b < c || d < a
distinct p@[(a,b)] ((c,d):ys)
    = if a > d then distinct p ys
               else distinct p [(c,d)]
distinct (x:xs) p
    = distinct [x] p && distinct xs p

addCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
addCs [p@(a,b)] [q@(c,d)] = if b < c then [p,q] else [q,p]
addCs p@[(a,b)] q@((c,d):ys)
    = if a > d then (c,d):addCs p ys
               else (a,b):q
addCs (x:xs) p
    = addCs xs (addCs [x] p)

combineCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
combineCs p@[(a,b)] q@[(c,d)] = if a < c then [(a,d)] else [(c,b)]
combineCs p@[(a,b)] q@((c,d):ys)
    = if a > d then (c,d):combineCs p ys
               else combineCs [(a,b)] [(c,d)] ++ ys
combineCs (x:xs) p
    = combineCs xs (combineCs [x] p)

intCombineCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
intCombineCs p@[(a,b)] q@[(c,d)] = if a < c then [(c,b)] else [(a,d)]
intCombineCs p@[(a,b)] q@((c,d):ys)
    = if c > b then ys
               else intCombineCs p [(c,d)] ++ intCombineCs p ys
intCombineCs (x:xs) p
    = intCombineCs xs (intCombineCs [x] p)

excCombineCs :: [(Integer,Integer)] -> [(Integer,Integer)] -> [(Integer,Integer)]
excCombineCs p@[(a,b)] q@[(c,d)] = if a < c then [(a,c-1)] else [(d+1,b)]
excCombineCs p@[(a,b)] q@((c,d):ys)
    = if c > b then []
               else excCombineCs (excCombineCs p [(c,d)]) ys
excCombineCs (x:xs) p
    = excCombineCs [x] p ++ excCombineCs xs p

lowerB :: [(Integer,Integer)] -> Integer
lowerB = fst . head

upperB :: [(Integer,Integer)] -> Integer
upperB = snd . last

elemOf :: Integer -> [(Integer,Integer)] -> Bool
elemOf l [] = False
elemOf l ((f,s):r)
        = l >= f && l <= s || elemOf l r

\end{code}

The type EM represents the existence or not of an extension marker in a size constraint.
The Maybe type is used because an extension marker may be followed by additional values or not.

\begin{code}

data EM = NoMarker | EM (Maybe Constraint)

evalEM (EM x) = x

type NamedBits = [NamedBit]

data NamedBit = NB String Integer

\end{code}

multiSize converts a multiply size-constrained type in to a single size-constrained type.
multiRSize is similar but removes any extensions since it will be
used in type assignment of an extensible type.
\begin{code}

multiSize :: ASNType a -> ASNType a
multiSize (SIZE t@(SIZE t' s' e') s e)
        = multiSize (SIZE t' (Intersection s' s) (unionEM e' e))
multiSize x = x


multiRSize :: ASNType a -> ASNType a
multiRSize (SIZE t@(SIZE t' s' e') s e)
        = multiRSize (SIZE t' (Intersection s' s) NoMarker)
multiRSize x = x


sizeLimit t@(SIZE _ _ _)
    = let SIZE _ s _  = multiSize t
          xs = evalCons s
          l = (fst . head) xs
          u = (snd . last) xs
      in
        Constrained (Just l) (Just u)
sizeLimit t
    = Constrained Nothing Nothing

unionEM NoMarker x = x
unionEM y NoMarker = y
unionEM (EM Nothing) x = x
unionEM y (EM Nothing) = y
unionEM (EM (Just s)) (EM (Just t)) = EM (Just (Union s t))

\end{code}

Type aliases used when defining a range-constrained Integer.

\begin{code}

type Upper = Maybe Integer
type Lower = Maybe Integer

\end{code}

The type Constrained is used to represent the lower and upper bounds of a range.
It is also returned by the function sizeLimit which returns the
upper and lower bounds on the size of a value.

\begin{code}

data Constrained a = Constrained (Maybe a) (Maybe a)
   deriving Show

instance Ord a => Monoid (Constrained a) where
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

bounds :: Ord a => ASNType a -> Constrained a
bounds (INCLUDES t1 t2)   = (bounds t1) `mappend` (bounds t2)
bounds (RANGE t l u)      = (bounds t) `mappend` (Constrained l u)
bounds _                  = Constrained Nothing Nothing

\end{code}


toPer is the top-level PER encoding function. It takes two inputs:
- the ASN type the value to be encoded; and
- the value to be encoded.

The first input is required both to indicate the encoding function
to be called and to provide extra input information when required for
the encoding function. For example, the encoding of a size-constrained value
depends on the range of possible size values which are supplied by
the first input.

toPer currently uses the function toPer8s to apply the relevant `multiple-of-8'
padding. This will be replaced with toPer functions that keep a running
counter.

\begin{code}

toPer :: ASNType a -> a -> BitStream
toPer (TYPEASS tr tg ct) v                      = toPer8s ct v
toPer (EXTADDGROUP s) x                         = toPerOpen (SEQUENCE s) x
toPer t@BOOLEAN x                               = encodeBool t x
toPer t@INTEGER x                               = encodeInt t x
toPer r@(RANGE i l u) x                         = encodeInt r x
toPer (ENUMERATED e) x                          = encodeEnum e x
toPer t@(BITSTRING nbs) x                       = encodeBS t x
toPer t@(SIZE (BITSTRING _) _ _) x              = encodeBS t x
toPer t@OCTETSTRING x                           = encodeOS t x
toPer t@(SIZE OCTETSTRING _ _) x            = encodeOS t x
toPer (SEQUENCE s) x                            = encodeSeq s x
toPer t@(SEQUENCEOF s) x                        = encodeSO t x
toPer t@(SIZE (SEQUENCEOF c) _ _) x             = encodeSO t x
toPer (SET s) x                                 = encodeSet s x
toPer t@(SETOF s) x                             = encodeSO t x
toPer t@(CHOICE c) x                            = encodeChoice c x
toPer t@VISIBLESTRING x                         = encodeVS t x
toPer t@NUMERICSTRING x                         = encodeNS t x
toPer IA5STRING x                               = []
-- IA5STRING to be encoded
toPer t@(SIZE VISIBLESTRING _ _) x              = encodeVS t x
toPer t@(SIZE NUMERICSTRING _ _) x              = encodeNS t x
toPer t@(FROM VISIBLESTRING pac) x              = encodeVSF t x
toPer t@(SIZE (FROM VISIBLESTRING pac) _ _) x   = encodeVSF t x
toPer t@(SIZE (SIZE _ _ _) _ _) x               = let nt = multiSize t
                                                  in
                                                      toPer nt x
toPer (SIZE (TYPEASS r tg t) s em) x            = let nt = multiRSize t
                                                  in
                                                      toPer (SIZE nt s em) x


toPer8s ct v
    = let bts = toPer ct v
          lbs = genericLength bts
          rb  = lbs `mod` 8
        in
            if null bts then [0,0,0,0,0,0,0,0]
        else if rb == 0
                     then bts
                     else
                       bts ++ take (8-rb) (repeat 0)

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
        encodeOctetsWithLength pad

\end{code}

11 ENCODING THE BOOLEAN TYPE

\begin{code}

encodeBool :: ASNType Bool -> Bool -> BitStream
encodeBool t True = [1]
encodeBool t _    = [0]

\end{code}

\section{10.3 -- 10.8 ENCODING THE INTEGER TYPE}

\begin{code}

encodeInt' :: ASNType Integer -> Integer -> BP.BitPut
encodeInt' t x =
   case p of
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1 in
            if range <= 1
               then return ()
               else encodeNNBIntBits' ((x-lb),range-1)
      Constrained (Just lb) Nothing ->
                encodeSCInt' x lb
      Constrained Nothing _ ->
                encodeUInt' x
   where
      p = bounds t

\end{code}

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

Note: we can do much better than put 1 bit a time!!! But this will do for
now.

\begin{code}

encodeNNBIntBits' :: (Integer, Integer) -> BP.BitPut
encodeNNBIntBits' =
   bitPutify . (map fromIntegral) . encodeNNBIntBits

bitPutify :: [Word8] -> BP.BitPut
bitPutify = mapM_ (BP.putNBits 1)
     
encodeNNBIntBitsAux (_,0) = Nothing
encodeNNBIntBitsAux (0,w) = Just (0, (0, w `div` 2))
encodeNNBIntBitsAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

\end{code}

\begin{code}

encodeNNBIntBits :: (Integer, Integer) -> BitStream
encodeNNBIntBits
    = reverse . (map fromInteger) . unfoldr encodeNNBIntBitsAux

\end{code}

 encodeNNBIntOctets encodes an integer in the minimum number of
 octets.

\begin{code}

encodeNNBIntOctets' :: Integer -> BP.BitPut
encodeNNBIntOctets' =
   bitPutify . (map fromIntegral) . encodeNNBIntOctets

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
 length encoding.

\begin{code}

encodeSCInt :: Integer -> Integer -> BitStream
encodeSCInt v lb
    = encodeOctetsWithLength (encodeNNBIntOctets (v-lb))

infixr 7 `c2`
c2 = (.).(.)

encodeSCInt' :: Integer -> Integer -> BP.BitPut
encodeSCInt' = bitPutify `c2` (map fromIntegral) `c2` encodeSCInt

\end{code}

 10.8 Encoding of an unconstrained integer. The integer is
 encoded as a 2's-complement-binary-integer with an explicit
 length encoding.

\begin{code}

encodeUInt :: Integer -> BitStream
encodeUInt x = encodeOctetsWithLength (to2sComplement x)

encodeUInt' :: Integer -> BP.BitPut
encodeUInt' = bitPutify . (map fromIntegral) . encodeUInt

\end{code}

10.9 General rules for encoding a length determinant
10.9.4, 10.9.4.2 and 10.9.3.4 to 10.9.3.8.4.

encodeWithLength takes a list of values (could be bits, octets or
any ASN.1 type), and groups them first in 16k batches, and then in
batches of 4. The input value-encoding function is then supplied as
an input to the function addUncLen which manages the interleaving of
length and value encodings -- it encodes the length and values of
each batch and concatenates their resulting bitstreams together.
Note the values are encoded using the input function.

\begin{code}

encodeWithLength' f = bitPutify . (map fromIntegral) . (encodeWithLength f)

encodeWithLength :: ([t] -> [Int]) -> [t] -> [Int]
encodeWithLength fun = addUncLen fun . groupBy 4 . groupBy (16*(2^10))

groupBy :: Int -> [t] -> [[t]]
groupBy n =
   unfoldr k
      where
         k [] = Nothing
         k p = Just (splitAt n p)

\end{code}

addUncLen is a HOF which encodes a value with an unconstrained
length i.e. it either has no upper bound on the size of the value,
or the upper bound is at least 64k. The inputs are the value encoding
function and the value represented as a collection of 4*16k
blocks.

lastLen encodes the length remainder modulo 16k and blocklen
encodes the length of a block (1 to 4).

\begin{code}

addUncLen :: ([b] -> [Int]) -> [[[b]]] -> [Int]
addUncLen encFun [] = lastLen 0
addUncLen encFun (x:xs)
    | l == 4 && last16 == k16 = blockLen 4 63 ++ (concat . map encFun) x
                                              ++ addUncLen encFun xs
    | l == 1 && last16 < k16  = lastLen ((genericLength . head) x) ++ encFun (head x)
    | otherwise               = if last16 == k16
                                    then blockLen l 63 ++ (concat . map encFun) x ++ lastLen 0
                                    else blockLen (l-1) 63 ++ (concat . map encFun) (init x)
                                                           ++ lastLen ((genericLength.last) x)
                                                           ++ encFun (last x)
    where
        l      = genericLength x
        last16 = (genericLength . last) x
        k16    = 16*(2^10)


lastLen :: Integer -> [Int]
lastLen n
   | n <= 127       = 0:(encodeNNBIntBits (n, 127))
   | n < 16*(2^10)  = 1:0:(encodeNNBIntBits (n, (16*(2^10)-1)))

blockLen :: Integer -> Integer -> [Int]
blockLen x y = (1:1:(encodeNNBIntBits (x,y)))

\end{code}

encodeOctetsWithLength encodes a collection of octets with
unconstrained length. encodeBitsWithLength does the same except
for a collection of bits.

\begin{code}

encodeOctetsWithLength' = bitPutify . (map fromIntegral). encodeOctetsWithLength

encodeOctetsWithLength :: [Int] -> [Int]
encodeOctetsWithLength = encodeWithLength (concat . id) . groupBy 8

encodeBitsWithLength' = bitPutify . (map fromIntegral). encodeBitsWithLength

encodeBitsWithLength :: [Int] -> [Int]
encodeBitsWithLength = encodeWithLength id

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

encodeSz encodes a size-constrained value. manageExtremes implements
16.6-16.8 (for OctetString) or 19.5-19.6 (for Sequence-of) which state
that no length encoding is used when the length is known and less than
64k, the length is encoded as an semi-constrained whole number if the
upper bound is unset (does not exist or at least 64k) and as a constrained
whole number otherwise.

Where an extension marker exists a single bit is added to the
front of the encoding. A 1 indicates that the size of the value is
not within the extension root and a 0 indicates otherwise. If the
value is not within the extension root then the length is encoded
as an unconstrained whole number.

\begin{code}

encodeSz :: ASNType t -> (ASNType t -> [a] -> BitStream)-> (ASNType t -> [a] -> BitStream) -> [a] -> BitStream
encodeSz (SIZE ty s NoMarker) noL yesL x
        =   let
                sv = evalCons s
                l  = lowerB sv
                u  = upperB sv
            in
                 manageExtremes (noL ty) (yesL ty) l u x
encodeSz (SIZE ty s (EM (Just c))) noL yesL x
        =   let
                sv  = evalCons s
                lx  = genericLength x
                b   = lx `elemOf` sv
                esv = sv `unionCs` evalCons c
                l   = lowerB esv
                u   = upperB esv
                en = manageExtremes (noL ty) (yesL ty) l u x
            in
                if b
                    then 0:en
                    else 1:yesL ty x


manageExtremes :: ([a] -> BitStream) -> ([a] -> BitStream) -> Integer -> Integer -> [a] -> BitStream
manageExtremes fn1 fn2 l u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
               then fn1 x
               else if u >= 65536
                   then fn2 x
                   else encodeNNBIntBits ((genericLength x-l),range-1) ++ fn1 x

\end{code}



\section{Two's Complement Arithmetic}

10.4 Encoding as a 2's-complement-binary-integer is used when
encoding an integer with no lower bound (10.8) as in the final
case of encodeInt. The encoding of the integer is accompanied
by the encoding of its length using encodeOctetsWithLength
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

\section{13. ENCODING THE ENUMERATED TYPE}

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


\section{15. ENCODING THE BITSTRING TYPE}


\begin{code}

encodeBS :: ASNType BitString -> BitString -> BitStream
encodeBS t@(SIZE ty s e) x = encodeBSSz t x
encodeBS t x               = encodeBSNoSz t x


encodeBSSz :: ASNType BitString -> BitString -> BitStream
encodeBSSz (SIZE (BITSTRING nbs) s NoMarker) (BitString xs)
    = let l   = lowerB (evalCons s)
          u   = upperB (evalCons s)
          exs = if (not.null) nbs then editBS l u xs
                  else xs
          ln  = genericLength exs
      in
                bsCode nbs s NoMarker exs
encodeBSSz (SIZE (BITSTRING nbs) s m@(EM (Just e))) (BitString xs)
    =   let ln = genericLength xs
            l  = lowerB (evalCons s)
            u  = upperB (evalCons s)
        in if ln <= u && ln >= l
                then 0: bsCode nbs s m xs
                else 1: bsCode nbs s m xs

-- update the above so that is tests whether ln is in the list of
-- pairs

bsCode nbs s m xs
      =  let (EM (Just ns)) = unionEM (EM (Just s)) m
             l  = lowerB (evalCons ns)
             u  = upperB (evalCons ns)
             exs = if (not.null) nbs then editBS l u xs
                     else xs
             ln = genericLength exs
         in
             if u == 0
             then []
             else if u == l && u <= 65536
                       then exs
                       else if u <= 65536
                            then encodeNNBIntBits ((ln-l), (u-l)) ++ exs
                            else encodeBitsWithLength exs


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
encodeBSNoSz (BITSTRING nbs) (BitString [])
    = [0,0,0,0,0,0,0,0]
encodeBSNoSz (BITSTRING nbs) (BitString bs)
    = let rbs = reverse bs
          rem0 = if (not.null) nbs then strip0s rbs
            else rbs
          ln = genericLength rem0
       in
        encodeBitsWithLength (reverse rem0)



strip0s (a:r)
    = if a == 0
        then strip0s r
        else (a:r)
strip0s [] = []
\end{code}

\section{16. ENCODING THE OCTETSTRING TYPE}

\begin{code}

encodeOS :: ASNType OctetString -> OctetString -> BitStream
encodeOS  t@(SIZE t' s e) (OctetString x) = encodeSz t encodeOSNoL encodeOctS x
encodeOS t (OctetString x)                = encodeOctS t x

\end{code}

encodeOctS encodes an unconstrained SEQUENCEOF value.

\begin{code}

encodeOctS :: ASNType OctetString -> [Octet] -> BitStream
encodeOctS s@OCTETSTRING xs
    = encodeOSWithLength s xs

\end{code}

encodeSOWithLength encodes a sequence-of value with the appropriate
length encoding.

\begin{code}

encodeOSWithLength :: ASNType OctetString -> [Octet] -> BitStream
encodeOSWithLength s = encodeWithLength
            (concat . map (let foo x = encodeNNBIntBits ((fromIntegral x),255) in foo))

\end{code}


No length encoding of SEQUENCEOF

\begin{code}

encodeOSNoL :: ASNType OctetString -> [Octet] -> BitStream
encodeOSNoL OCTETSTRING xs
    = (concat . map (let foo x = encodeNNBIntBits ((fromIntegral x),255) in foo)) xs

\end{code}

\section{18. ENCODING THE SEQUENCE TYPE}

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
        else 1:encodeOctetsWithLength (encodeNNBIntOctets la) ++ concat ap

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

encodeCO implments the encoding of a COMPONENTS OF component of a
sequence. The (non-extension) components of the referenced
sequence are embedded in the parent sequence and are enocoded as
if components of this sequence.

\begin{code}

encodeSeqAux :: ([BitStream],[BitStream]) -> ([BitStream],[BitStream]) -> Sequence a -> a ->
    (([BitStream],[BitStream]),([BitStream],[BitStream]))
encodeSeqAux (ap,ab) (rp,rb) Nil _
    = if ((not.null) (concat ab))
        then (([1]:reverse rp,reverse rb),(reverse ap,reverse ab))
        else ((reverse rp,reverse rb),(reverse ap, reverse ab))
encodeSeqAux (ap,ab) (rp,rb) (Extens as) xs
    = encodeExtSeqAux (ap,ab) (rp,rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTCompOf (TYPEASS tr ti (SEQUENCE s))) as) (x:*:xs) =
    let (p,b) = encodeCO ([],[]) s x
    in
        encodeSeqAux (ap,ab) (p ++ rp,b ++ rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTMandatory (NamedType n t a)) as) (x:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([1]:rp,toPer a x:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Just x:*:xs) =
   encodeSeqAux (ap,ab) ([1]:rp,toPer a x:rb) as xs

encodeCO :: ([BitStream],[BitStream]) -> Sequence a -> a -> (([BitStream],[BitStream]))
encodeCO (rp,rb) Nil _
    = (rp,rb)
encodeCO (rp,rb) (Extens as) xs
    = encodeExtCO (rp,rb) as xs
encodeCO (rp,rb) (Cons (CTCompOf (TYPEASS tr ti (SEQUENCE s))) as) (x:*:xs) =
    let (p,b) = encodeCO ([],[]) s x
    in
        encodeCO (p ++ rp,b ++ rb) as xs
encodeCO (rp,rb) (Cons (CTMandatory (NamedType n t a)) as) (x:*:xs) =
   encodeCO ([]:rp,toPer a x:rb) as xs
encodeCO (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Nothing:*:xs) =
   encodeCO ([]:rp,[]:rb) as xs
encodeCO (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Just x:*:xs) =
   encodeCO ([]:rp,toPer a x:rb) as xs
encodeCO (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Just x:*:xs) =
   encodeCO ([1]:rp,toPer a x:rb) as xs
encodeCO (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Just x:*:xs) =
   encodeCO ([1]:rp,toPer a x:rb) as xs


encodeExtCO :: ([BitStream],[BitStream]) -> Sequence a -> a -> (([BitStream],[BitStream]))
encodeExtCO (rp,rb) Nil _
    = (rp,rb)
encodeExtCO (rp,rb) (Extens as) xs
    = encodeCO (rp,rb) as xs
encodeExtCO (rp,rb) (Cons _ as) (_:*:xs)
    = encodeExtCO (rp,rb) as xs

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
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTExtMand (NamedType n t a)) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTOptional (NamedType n t a)) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (Cons (CTDefault (NamedType n t a) d) as) (Just x:*:xs) =
   encodeExtSeqAux ([1]:ap,toPerOpen a x:ab) (rp,rb) as xs

\end{code}


19. ENCODING THE SEQUENCE-OF TYPE

encodeSO implements the encoding of an unconstrained
sequence-of value. This requires both the encoding of
each of the components, and in most cases the encoding
of the length of the sequence-of (which may require
fragmentation into 64K blocks).

\begin{code}

encodeSO :: ASNType [a] -> [a] -> BitStream
encodeSO  t@(SIZE t' s e) x = encodeSz t encodeSONoL encodeSeqOf x
encodeSO t x = encodeSeqOf t x

\end{code}

encodeSeqOf encodes an unconstrained SEQUENCEOF value.

\begin{code}

encodeSeqOf :: ASNType [a] -> [a] -> BitStream
encodeSeqOf (SEQUENCEOF s) xs
    = encodeSOWithLength s xs

\end{code}

encodeSOWithLength encodes a sequence-of value with the appropriate
length encoding.

\begin{code}
encodeSOWithLength :: ASNType a -> [a] -> BitStream
encodeSOWithLength s = encodeWithLength (concat . map (toPer s))

\end{code}


No length encoding of SEQUENCEOF

\begin{code}

encodeSONoL :: ASNType a -> a -> BitStream
encodeSONoL (SEQUENCEOF s) xs
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
getTags (Cons a xs)       = getCTI a : getTags xs


getTags' :: Sequence a -> [TagInfo]
getTags' Nil         = []
getTags' (Extens xs) = getTags xs
getTags' (Cons a xs) = getTags' xs


getCTI :: ComponentType a -> TagInfo
getCTI (CTMandatory (NamedType _ Nothing ct))   = getTI ct
getCTI (CTMandatory (NamedType _ (Just t) ct))  = t
getCTI (CTExtMand (NamedType _ Nothing ct))     = getTI ct
getCTI (CTExtMand (NamedType _ (Just t) ct))    = t
getCTI (CTOptional (NamedType _ Nothing ct))   = getTI ct
getCTI (CTOptional (NamedType _ (Just t) ct))  = t
getCTI (CTDefault (NamedType _ Nothing ct) d)  = getTI ct
getCTI (CTDefault (NamedType _ (Just t) ct) d) = t

getTI :: ASNType a -> TagInfo
getTI (TYPEASS _ (Just tg) _)   = tg
getTI (TYPEASS _ _ t)           = getTI t
getTI BOOLEAN                   = (Universal, 1, Explicit)
getTI INTEGER                   = (Universal,2, Explicit)
getTI (RANGE c _ _)             = getTI c
getTI IA5STRING                 = (Universal,22, Explicit)
getTI (BITSTRING _)             = (Universal, 3, Explicit)
getTI PRINTABLESTRING           = (Universal, 19, Explicit)
getTI VISIBLESTRING             = (Universal, 26, Explicit)
getTI NUMERICSTRING             = (Universal, 18, Explicit)
getTI (SEQUENCE s)              = (Universal, 16, Explicit)
getTI (SEQUENCEOF s)            = (Universal, 16, Explicit)
getTI (SET s)                   = (Universal, 17, Explicit)
getTI (SETOF s)                 = (Universal, 17, Explicit)
getTI (SIZE c _ _ )             = getTI c
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

encodeChoice :: Choice a -> HL a (S Z) -> BitStream
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
                    else ea ++ 1:encodeOctetsWithLength (encodeNNBIntOctets (fst fr)) ++ (snd.snd) fr

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
        = getCTI v : getCTags (ChoiceOption (NamedType n t (EXTADDGROUP rs))xs)
getCTags (ChoiceOption (NamedType n t (EXTADDGROUP Nil)) xs)
        = getCTags xs
getCTags (ChoiceOption (NamedType n Nothing a) xs)
        = getTI a : getCTags xs
getCTags (ChoiceOption (NamedType n (Just t) a) xs)
        = t : getCTags xs

choicePred :: (TagInfo, BitStream) -> (TagInfo, BitStream) -> Bool
choicePred (t1,_) (t2,_) = t1 <= t2


encodeChoiceAux :: [Int] -> [BitStream] -> Choice a -> HL a n -> ([Int], [BitStream])
encodeChoiceAux ext body NoChoice _ = (ext, reverse body)
encodeChoiceAux ext body (ChoiceExt as) xs =
   encodeChoiceExtAux [0] body as xs
encodeChoiceAux ext body (ChoiceOption a as) (NoValueC x xs) =
   encodeChoiceAux ext ([]:body) as xs
encodeChoiceAux ext body (ChoiceOption (NamedType n t a) as) (ValueC x xs) =
   encodeChoiceAux' ext ((toPer a x):body) as xs


encodeChoiceAux' :: [Int] -> [BitStream] -> Choice a -> HL a n -> ([Int], [BitStream])
encodeChoiceAux' ext body NoChoice _ = (ext, reverse body)
encodeChoiceAux' ext body (ChoiceExt as) xs =
   encodeChoiceExtAux' ext body as xs
encodeChoiceAux' ext body (ChoiceOption a as) (NoValueC x xs) =
   encodeChoiceAux' ext ([]:body) as xs
encodeChoiceAux' ext body (ChoiceOption a as) (ValueC x xs) =
   encodeChoiceAux' ext ([]:body) as xs


encodeChoiceExtAux :: [Int] -> [BitStream] -> Choice a -> HL a n -> ([Int], [BitStream])
encodeChoiceExtAux ext body NoChoice _ = (ext,reverse body)
encodeChoiceExtAux ext body (ChoiceExt as) xs =
   encodeChoiceAux ext body as xs
encodeChoiceExtAux ext body (ChoiceEAG as) xs =
   encodeChoiceExtAux ext body as xs
encodeChoiceExtAux ext body (ChoiceOption a as) (NoValueC x xs) =
   encodeChoiceExtAux ext ([]:body) as xs
encodeChoiceExtAux ext body (ChoiceOption (NamedType n t a) as) (ValueC x xs) =
   encodeChoiceExtAux' [1]((toPerOpen a x):body) as xs

encodeChoiceExtAux' :: [Int] -> [BitStream] -> Choice a -> HL a n -> ([Int], [BitStream])
encodeChoiceExtAux' ext body NoChoice _ = (ext, reverse body)
encodeChoiceExtAux' ext body (ChoiceExt as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceEAG as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceOption a as) (NoValueC x xs) =
   encodeChoiceExtAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceOption a as) (ValueC x xs) =
   encodeChoiceExtAux' ext body as xs


\end{code}

 27. Encoding the restricted character string types (VISIBLESTRING)

\begin{code}
encodeVS :: ASNType VisibleString -> VisibleString -> BitStream
encodeVS t@(SIZE _ _ _) x = encodeVisSz t x
encodeVS t x = encodeVis t x

encodeVisSz :: ASNType VisibleString -> VisibleString -> BitStream
encodeVisSz t@(SIZE ty s _) x@(VisibleString xs)
    = let l = lowerB (evalCons s)
          u = upperB (evalCons s)
      in
          manageExtremes encS (encodeVis ty . VisibleString) l u xs


encodeVis :: ASNType VisibleString -> VisibleString -> BitStream
encodeVis vs (VisibleString s)
    = encodeWithLength encS s


encC c  = encodeNNBIntBits ((toInteger . ord) c, 94)
encS s  = (concat . map encC) s

\end{code}

 27.5.4 Encoding of a VISIBLESTRING with a permitted alphabet
 constraint.

\begin{code}

encodeVSF :: ASNType VisibleString -> VisibleString -> BitStream
encodeVSF (SIZE t@(FROM _ _) _ _) x = encodeVisSzF t x
encodeVSF v@(FROM _ _) x = encodeVisF v x

encodeVisSzF :: ASNType VisibleString -> VisibleString -> BitStream
encodeVisSzF (SIZE ty@(FROM cv pac) s e) x@(VisibleString xs)
        =   let l = lowerB (evalCons s)
                u = upperB (evalCons s)
            in
                manageExtremes (encSF pac) (encodeVisF ty . VisibleString) l u xs


encodeVisF :: ASNType VisibleString -> VisibleString -> BitStream
encodeVisF vs@(FROM cv pac) (VisibleString s)
    = encodeWithLength (encSF pac) s

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
encodeNS t@(SIZE _ _ _) x = encodeNumSz t x
encodeNS t x              = encodeNum t x

encodeNumSz :: ASNType NumericString -> NumericString -> BitStream
encodeNumSz t@(SIZE ty s _) x@(NumericString xs)
    = let l = lowerB (evalCons s)
          u = upperB (evalCons s)
      in
          manageExtremes encNS (encodeNum ty . NumericString) l u xs





encodeNum :: ASNType NumericString -> NumericString -> BitStream
encodeNum ns (NumericString s)
    = encodeWithLength encNS s

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

mmGetBit :: (Integral x, MonadState (B.ByteString,x) m, MonadError String m) => m Word8
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
         ys = B.drop (fromIntegral nBytes) xs
         z = B.head ys
         u = (z .&. ((2^(7 - nBits)))) `shiftR` (fromIntegral (7 - nBits))

mmGetBits :: (Integral x, MonadState (B.ByteString,x) m, MonadError String m, Integral n) => n -> m [Word8]
mmGetBits n =
   sequence (genericTake n (repeat mmGetBit))

\end{code}

\subsection{Length Determinant}

This function decodes the length determinant as defined in 10.9.
It does not currently cover 10.9.3.4: the determinant being a normally small length.

Note that it assumes that the ASN.1 type makes semantic sense.
For example, if the upper bound of the size constraint ("ub") is 0 and the
lower bound ("lb") is negative, then the result is undefined.

\begin{code}

decodeLengthDeterminant ::
   (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
      Constrained Integer -> (Integer -> ASNType a -> m [b]) -> ASNType a -> m [b]
decodeLengthDeterminant (Constrained lb ub) f t
   | ub /= Nothing && ub == lb && ub <= (Just n64k) = f (fromJust ub) t
   | ub == Nothing = decodeLargeLengthDeterminant f t
   | ub <= (Just n64k) = do l <- mFromPer (RANGE INTEGER lb ub)
                            f l t
   | otherwise = decodeLargeLengthDeterminant f t

\end{code}

This function decodes the length determinant for unconstrained length or large "ub".
See 10.9.4 and 10.9.3.4 -- 10.9.3.8.4 for further details. Note that we don't currently
cover 10.9.3.4!!! It does so by taking a function which itself takes an iteration count,
an ASN.1 type and returns a (monadic) list of decoded values which may or may not be
values of the ASN.1 type.

\begin{code}

decodeLargeLengthDeterminant ::
   (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
      (Integer -> ASNType a -> m [b]) -> ASNType a -> m [b]
decodeLargeLengthDeterminant f t =
   do p <- mmGetBit
      case p of
         0 ->
            do j <- mmGetBits 7
               let l = fromNonNeg j
               f l t
         1 ->
            do q <- mmGetBit
               case q of
                  0 ->
                     do j <- mmGetBits 14
                        let l = fromNonNeg j
                        f l t
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError (fragError ++ show fragSize)
                           else do frag <- f (fragSize * n16k) t
                                   rest <- decodeLargeLengthDeterminant f t
                                   return (frag ++ rest)
                        where
                           fragError = "Unable to decode with fragment size of "

{-
decodeLargeLengthDeterminant' ::
   (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
      (Integer -> ASNType a -> m [b]) -> ASNType a -> m [b]
-}
decodeLargeLengthDeterminant' f t =
   do p <- BG.getBit
      if (not p) 
         then
            do j <- BG.getLeftByteString 7
               let l = fromNonNeg' 7 j
               f l t
         else
            error "you are here"
{-
         1 ->
            do q <- mmGetBit
               case q of
                  0 ->
                     do j <- mmGetBits 14
                        let l = fromNonNeg j
                        f l t
                  1 ->
                     do j <- mmGetBits 6
                        let fragSize = fromNonNeg j
                        if fragSize <= 0 || fragSize > 4
                           then throwError (fragError ++ show fragSize)
                           else do frag <- f (fragSize * n16k) t
                                   rest <- decodeLargeLengthDeterminant f t
                                   return (frag ++ rest)
                        where
                           fragError = "Unable to decode with fragment size of "
-}

\end{code}

\subsection{INTEGER}

Constrained {\em INTEGER}s are encoded as non-negative binary in
the least number of bits
unless the range is 1 (in which case the answer is the lower and upper bound) --- see Note 2 in Clause 12.

Semi-constrained and unconstrained {\em INTEGER}s are encoded in a list of chunks of
8 bits (octets) as non-negative binary or as two's complement respectively with a
\lq\lq large\rq\rq\ length determinant (as there are no constraints on the length
determinant itself in this particular case).

\begin{code}

fromPerInteger t =
   case p of
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1
             n     = genericLength (encodeNNBIntBits ((ub-lb),range-1)) in
            if range <= 1
               then return lb
               else do j <- mmGetBits n
                       return (lb + (fromNonNeg j))
      Constrained (Just lb) Nothing ->
         do o <- octets
            return (lb + (fromNonNeg o))
      Constrained Nothing _ ->
         do o <- octets
            return (from2sComplement o)
   where
      p        = bounds t
      octets   = decodeLargeLengthDeterminant chunkBy8 undefined
      chunkBy8 = flip (const (mmGetBits . (*8)))

\end{code}

{\em fromNonNeg'} works on bits and when the {\em INTEGER is} semi-constrained
we know the value is in octets so we can use something which works on e.g.
{\em Word8} which should be more efficient.

Oh and we should write a QuickCheck test for {\em fromNonNeg'}.

\begin{code}

fromPerInteger' t =
   case p of
      Constrained (Just lb) (Just ub) ->
         let range = ub - lb + 1
             n     = genericLength (encodeNNBIntBits ((ub-lb),range-1)) in
            if range <= 1
               then return lb
               else do j <- BG.getLeftByteString n
                       return (lb + (fromNonNeg' n j))
      Constrained (Just lb) Nothing ->
         do o <- octets
            let n = 8 * (B.length o)
            return (lb + (fromNonNeg' n o))
      Constrained Nothing _ ->
         do o <- octets
            return (from2sComplement' o)
   where
      p        = bounds t
      octets   = decodeLargeLengthDeterminant' chunkBy8 undefined
      chunkBy8 = flip (const (BG.getLeftByteString . (*8)))

\end{code}

\subsection{BIT STRING --- Clause 15}

{\em BIT STRING}s are encoded with a length determinant but the type
is immaterial hence we use $\bottom$ as the type argument to
{\em decodeLengthDeterminant}; the (function) argument to
decode the individual components merely takes 1 bit at a time.

\begin{code}

fromPerBitString t =
   decodeLengthDeterminant (sizeLimit t) chunkBy1 undefined
      where chunkBy1 = flip (const mmGetBits)

\end{code}

\subsection{OCTET STRING --- Clause 16}

{\em OCTET STRING}s are encoded with a length determinant but the type
is immaterial hence we use $\bottom$ as the type argument to
{\em decodeLengthDeterminant}; the (function) argument to
decode the individual components merely takes 8 bits at a time.

\begin{code}

fromOctetString t =
   decodeLengthDeterminant (sizeLimit t) chunkBy8 undefined
      where chunkBy8 = flip (const (mmGetBits . (*8)))

\end{code}


\section{Twos Complement Stuff}

{\em from2sComplement} will give an invalid answer for the empty list.
However, it is only used with a list of bits obtained from
{\em mmDecodeWithLengthDeterminant} which never returns an empty list
(it will produce an error if there are not enough bits).

\begin{code}

from2sComplement a@(x:xs) =
   -((fromIntegral x)*(2^(l-1))) + sum (zipWith (*) (map fromIntegral xs) ys)
   where
      l = genericLength a
      ys = map (2^) (f (l-2))
      f 0 = [0]
      f x = x:(f (x-1))

from2sComplement' a = x
   where
      l = fromIntegral (B.length a)
      b = l*8 - 1 
      (z:zs) = B.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

fromNonNeg xs =
   sum (zipWith (*) (map fromIntegral xs) ys)
   where
      l = genericLength xs
      ys = map (2^) (f (l-1))
      f 0 = [0]
      f x = x:(f (x-1))

bottomNBits :: Int -> Word8
bottomNBits 0 = 0
bottomNBits 1 = 0x01
bottomNBits 2 = 0x03
bottomNBits 3 = 0x07
bottomNBits 4 = 0x0f
bottomNBits 5 = 0x1f
bottomNBits 6 = 0x3f
bottomNBits 7 = 0x7f
bottomNBits 8 = 0xff
bottomNBits x = error ("bottomNBits undefined for " ++ show x)

rightShift :: Int -> B.ByteString -> B.ByteString
rightShift 0 = id
rightShift n = snd . B.mapAccumL f 0 where
  f acc b = (b .&. (bottomNBits n), (b `shiftR` n) .|. (acc `shiftL` (8 - n)))

fromNonNeg' r x = 
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` bSize
      bSize = bitSize (head ys)
      ys = reverse (B.unpack (rightShift s x))
      zs = map ((2^bSize)^) [0..genericLength ys]

\end{code}

\section{Decoding}

      -- fromIntegral for now until we sort out why there's a Word8 / Int clash

      -- This is a space leak waiting to happen

\begin{code}

mFromPer :: (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) => ASNType a -> m a
mFromPer t@INTEGER                 = fromPerInteger t
mFromPer r@(RANGE i l u)           = fromPerInteger r
mFromPer t@(BITSTRING _)           = (liftM (BitString . map fromIntegral) . fromPerBitString) t
mFromPer t@(SIZE (BITSTRING _) _ _) =
   (liftM (BitString . map fromIntegral) . fromPerBitString) t
mFromPer (SEQUENCE s)              =
   do ps <- mmGetBits (l s)
      mmFromPerSeq (map fromIntegral ps) s
   where
      l :: Integral n => Sequence a -> n
      l Nil = 0
      l (Cons (CTMandatory _) ts) = l ts
      l (Cons (CTOptional _ ) ts) = 1+(l ts)
mFromPer t@(SIZE (SIZE _ _ _) _ _) =
   let nt = multiSize t in mFromPer nt
mFromPer (SEQUENCEOF u)        = fromPerSeqOf u
mFromPer t@(SIZE (SEQUENCEOF u) _ _) = decodeLengthDeterminant (sizeLimit t) nSequenceOfElements u
mFromPer t@(CHOICE c) =
   do ps <- mmGetBits ((genericLength (encodeNNBIntBits (0,(l c) - 1))))
      decodeChoice (map fromIntegral ps) c
   where
      l :: Integral n => Choice a -> n
      l NoChoice = 0
      l (ChoiceOption t ts) = 1+(l ts)

\end{code}

\subsection{SEQUENCE}

   -- The bitmap always matches the Sequence but we recurse the Sequence twice so this needs to be fixed

I'm not really sure if this is true now having thought about it

\begin{code}

mmFromPerSeq :: (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) => BitStream -> Sequence a -> m a
mmFromPerSeq _ Nil = return Empty
mmFromPerSeq bitmap (Cons (CTMandatory (NamedType _ _ t)) ts) =
   do x <- mFromPer t
      xs <- mmFromPerSeq bitmap ts
      return (x:*:xs)
mmFromPerSeq bitmap (Cons (CTOptional (NamedType _ _ t)) ts) =
   do if (head bitmap) == 0
         then
            do xs <- mmFromPerSeq (tail bitmap) ts
               return (Nothing:*:xs)
         else
            do x <- mFromPer t
               xs <- mmFromPerSeq (tail bitmap) ts
               return ((Just x):*:xs)

\end{code}

\subsection{SEQUENCE OF}

\begin{code}

fromPerSeqOf ::
   (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
      ASNType a -> m [a]
fromPerSeqOf = decodeLargeLengthDeterminant nSequenceOfElements

nSequenceOfElements n = sequence . genericTake n . repeat . mFromPer

\end{code}

\begin{enumerate}

\item


The first condition deals with 19.5.

\end{enumerate}

\subsection{CHOICE}

Note we never have negative indices so we don't need to check for $n < 0$.

\begin{code}

decodeChoice :: (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
                   BitStream -> Choice a -> m (HL a (S Z))
decodeChoice bitmap c =
   case m of
      Nothing -> throwError ("Unable to select component. Probable cause: index too large")
      Just k ->
         nthChoice k c
      where
         ts = getCTags c
         us = sort ts
         n  = fromNonNeg bitmap
         m  = lookup (us!!n) (zip ts [0..])

nthChoice :: (Integral x, MonadState (B.ByteString,x) m, MonadError [Char] m) =>
                Integer -> Choice a -> m (HL a (S Z))
nthChoice n NoChoice =
   throwError ("Unable to select component. Probable cause: index too large")
nthChoice 0 (ChoiceOption nt@(NamedType _ _ t) cs) =
   do v <- mFromPer t
      let vs = noChoice cs
      return (ValueC v vs)
nthChoice n (ChoiceOption nt@(NamedType _ _ t) cs) =
   do v <- nthChoice (n - 1) cs
      return (NoValueC NoValue v)

noChoice :: Choice a -> HL a Z
noChoice NoChoice = EmptyHL
noChoice (ChoiceOption v vs) = NoValueC NoValue (noChoice vs)

\end{code}

\end{document}
