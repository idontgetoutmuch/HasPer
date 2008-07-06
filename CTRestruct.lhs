\documentclass{article}
%include polycode.fmt

\newcommand{\bottom}{\perp}

\begin{document}

\section{Introduction}

The encoding is for UNALIGNED PER

\begin{code}
{-# OPTIONS_GHC -XGADTs -XTypeOperators -XEmptyDataDecls -XFlexibleInstances -XFlexibleContexts #-}

module CTRestruct where

import qualified Data.Map as Map
import Data.List hiding (groupBy)
import Data.Bits
import Data.Char
import Control.Monad.State
import Control.Monad.Error
import qualified Data.ByteString as B
import Data.Binary.Strict.BitUtil (rightShift)
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.Strict.BitPut as BP
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String, ComponentType(Default), NamedType, OctetString)
import Text.PrettyPrint
import System
import IO
import Data.Int
import Data.Bits
import Data.Word
import Data.Maybe
import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Traversable as T
import Control.Applicative
\end{code}

We need to mimic the ASN.1 {\tt Type} as defined in X.680

An ASN.1 module is a collection of (mainly type) assignments. A
type assignment associates a type reference with a type where a type reference is simply an
identifier.

A {\tt Type} is:
\begin{itemize}
\item
a {\tt BuiltinType} -- any of the standard ASN.1 types or a tagged type;
\item
a {\tt ReferencedType} -- a (qualified or unqualified) type
reference or a parameterised type (defined in X.683); or
\item
a {\tt ConstrainedType} -- a type with a constraint.
\end{itemize}


A {\tt ReferencedType} is:
\begin{itemize}
\item
a {\tt DefinedType} -- this is either a qualifed (using a module reference) type reference,
a type reference, a parameterized type or a parameterized value
set type.
\item
a {\tt UsefulType} -- a collection of predefined types such as
\begin{verbatim}
GeneralizedTime ::= [UNIVERSAL 24] IMPLICIT VisibleString
\end{verbatim}
\item
a {\tt SelectionType} -- a type selected from a {\tt Choice} type.
\item
a {\tt TypeFromObject} -- a type from an information object (see X.681) or
\item
a {\tt ValueSetFromObjects} -- a value set from objects (see
X.681).
\end{itemize}

A {\tt ConstrainedType} is either a
\begin{itemize}
\item
a type associated with a {\tt Constraint} or
\item
a {\tt SETOF} or {\tt SEQUENCEOF} type with a constraint on the collection
type. That is, the usual type constraint construct implies that
the constraint is applied to the component type of a collection
type, and not to the collection itself.
\end{itemize}

A {\tt Constraint} is either a {\tt SubtypeConstraint} or a {\tt
GeneralConstraint} with or without an exception.

A {\tt SubtypeConstraint} may be extensible as indicated by {\tt
...} and is defined in X.680 using the type {\tt ElementSetSpecs}
as
\begin{verbatim}
ElementSetSpecs ::=
    RootElementSetSpec
    | RootElementSetSpec "," "..."
    | RootElementSetSpec "," "..." "," AdditionalElementSetSpec

RootElementSetSpec ::= ElementSetSpec

AdditionalElementSetSpec ::= ElementSetSpec

ElementSetSpec ::= Unions
    | ALL Exclusions

Unions ::= Intersections
    | UElems UnionMark Intersections

UElems ::= Unions

Intersections ::= IntersectionElements
    | IElems IntersectionMark IntersectionElements

IElems ::= Intersections

IntersectionElements ::= Elements | Elems Exclusions

Elems ::= Elements

Exclusions ::= EXCEPT Elements

UnionMark ::= "|" | UNION

IntersectionMark ::= "^" | INTERSECTION
\end{verbatim}
In summary a {\tt SubtypeConstraint} is either a union of
intersections of atomic constraints (such as single value, range and size) or everything except a subset of
values of a type. A {\tt GeneralConstraint} is defined in X.682.

Definition of Constraint Type

\begin{code}
-- This current version of the constraint type has ignored exceptions (see X.680 45.6)

data ESS a = RE (Constr a) | EXT (Constr a) | EXTWITH (Constr a) (Constr a)

data Constr a = UNION (Union a) | ALL (Excl a)

data Union a = IC (IntCon a) | UC (Union a) (IntCon a)

data IntCon a = INTER (IntCon a) (IE a) | ATOM (IE a)

data Excl a = EXCEPT (Elem a)

data IE a = E (Elem a) | Exc (Elem a) (Excl a)

data Elem a = S (SV a) | C (CT a) | V (VR a) | SZ (Sz a) | P (PA a)

data SV a = SingleValue a => SV a

data CT a = ContainedSubtype a => Inc (ASNType a)

data VR a = ValueRange a => R (a,a)

data Sz a = SizeConstraint a => SC (ESS Int)

data PA a = PermittedAlphabet a => FR (ESS a)

--IS to be completed for multiple type constraints
data IS a = InnerType a => WC (ESS a) | WCS

-- Type constraint (constraining an open type) to be done (47.6)
-- Pattern constraint to be done.

exC1 :: ESS Int
exC1 = RE (UNION (IC (ATOM (E (S (SV 7))))))
exC2 :: ESS Int
exC2  = RE (UNION (IC (INTER (ATOM (E (V (R (0,7))))) (E (V (R (1,10)))))))

\end{code}

Old version of Name (X.691 A2.1)

name
    = TYPEASS "Name" (Just (Application, 1, Implicit))
        (SEQUENCE
          (Cons (CTMandatory (NamedType "givenName" Nothing nameString))
            (Cons (CTMandatory (NamedType "initial" Nothing (SIZE nameString (Elem (1,1)) NoMarker)))
              (Cons (CTMandatory (NamedType "familyName" Nothing nameString)) Nil))))


New version of Name
\begin{code}
nameString :: ASNType VisibleString
nameString = RT (Ref "nameString")

assoc :: ASNType a -> ASNType a -> (String, ASNType a)
assoc (RT (Ref n)) t = (n,t)

name
    = BT (TAGGED (Application,1,Implicit)
            (SEQUENCE
                (Cons (CTMandatory (NamedType "givenName" Nothing nameString))
                    (Cons (CTMandatory (NamedType "initial" Nothing (ConsT nameString
                            (RE (UNION (IC (ATOM (E (SZ (SC ( RE( UNION (IC (ATOM (E (V (R (1,1))))))))))))))))))
                        (Cons (CTMandatory (NamedType "familyName" Nothing nameString)) Nil)))))

\end{code}
X.680 16.1

Type ::= BuiltinType | ReferencedType | ConstrainedType

\begin{code}
data ASNType a {- :: * -> * -} where
    BT    :: ASNBuiltin a -> ASNType a
    RT    :: ReferencedType -> ASNType a
    ConsT :: ASNType a -> ESS a -> ASNType a

data ASNBuiltin a {- :: * -> * -} where
   EXTADDGROUP     :: Sequence a -> ASNBuiltin a
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin Int
   ENUMERATED      :: Enumerate a -> ASNBuiltin a
   BITSTRING       :: NamedBits -> ASNBuiltin BitString
   OCTETSTRING     :: ASNBuiltin OctetString
   PRINTABLESTRING :: ASNBuiltin PrintableString
   IA5STRING       :: ASNBuiltin IA5String
   VISIBLESTRING   :: ASNBuiltin VisibleString
   NUMERICSTRING   :: ASNBuiltin NumericString
   SEQUENCE        :: Sequence a -> ASNBuiltin a
   SEQUENCEOF      :: ASNBuiltin a -> ASNBuiltin [a]
   SET             :: Sequence a -> ASNBuiltin a
   SETOF           :: ASNBuiltin a -> ASNBuiltin [a]
   CHOICE          :: Choice a -> ASNBuiltin (HL a (S Z))
   TAGGED          :: TagInfo -> ASNBuiltin a -> ASNBuiltin a


data ReferencedType = Ref TypeRef
\end{code}




Some newtype declarations used to define ASNBuiltin, and type aliases to make the code more readable.

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
instance SingleValue Int

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype IA5String
instance ContainedSubtype PrintableString
instance ContainedSubtype NumericString
instance ContainedSubtype Int

class ValueRange a

instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange Int


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


class InnerType a

instance InnerType (Choice a)
instance InnerType  (Sequence a)
instance InnerType [a]
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
data Sequence a {- :: * -> * -} where
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

data ComponentType a {- :: * -> * -} where
   CTMandatory :: NamedType a -> ComponentType a
   CTExtMand   :: NamedType a -> ComponentType (Maybe a)
   CTOptional  :: NamedType a -> ComponentType (Maybe a)
   CTDefault   :: NamedType a -> a -> ComponentType (Maybe a)
   CTCompOf    :: ASNType a   -> ComponentType a

data NamedType a {- :: * -> * -} where
   NamedType :: Name -> Maybe TagInfo -> ASNType a -> NamedType a

\end{code}

X.680 Section 28. Choice type

A choice is a collection of named types. The Choice type
is similar to a Sequence except that each value
is optional and only one value can exist at a time. Note
that the Choice type has no PER-visible constraints.
The constructors ChoiceExt and ChoiceEAG deal with
extension markers and extension addition groups respectively.

In order to enforce one and only one value for a choice the ASNBuiltin
constructor CHOICE returns a value of the type
ASNBuiltin (HL a (S Z)).

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

data Choice a {- :: * -> * -} where
    NoChoice     :: Choice Nil
    ChoiceExt    :: Choice l -> Choice l
    ChoiceEAG    :: Choice l -> Choice l
    ChoiceOption :: NamedType a -> Choice l -> Choice (a:*:l)

data HL a l {- :: * -> * -> * -} where
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

data EnumerationItem a {- :: * -> * -} where
    Identifier :: Name -> EnumerationItem Name
    NamedNumber :: Name -> Int -> EnumerationItem Name

data Enumerate a {- :: * -> * -} where
    NoEnum      :: Enumerate Nil
    EnumOption  :: EnumerationItem a -> Enumerate l -> Enumerate ((Maybe a):*:l)
    EnumExt     :: Enumerate l -> Enumerate l

\end{code}




\begin{code}

type NamedBits = [NamedBit]

data NamedBit = NB String Int

\end{code}

This is dross left over from previous thinking

Need a mechanism for associating type references with types.

-- \begin{code}
data HostType :: * where
    MV :: ASNType a -> HostType

refHost :: Map.Map TypeRef HostType
refHost = Map.empty

addRef1 = Map.insert "test1" (MV (BT INTEGER)) refHost
addRef2 = Map.insert "test2" (MV (BT BOOLEAN)) addRef1

getType :: TypeRef -> Map.Map TypeRef HostType -> HostType
getType tr host =  host Map.! tr



-- \end{code}

PER Top-Level encode function. There are three cases:
i.   The input is a builtin type: toPer is called on this type.
ii.  The input is a referenced type: the type has to be retrieved
and encode recursively called on this type.
iii. The input is a constrained type: the per-visible constraints
are filtered and the function called again on the type that is
constrained. Note that PER relies on effective constraints which
may differ from the ASN.1 view of a constraint. For example, the
serial application of (ALL EXCEPT (20..22)) and (10..30) on the
Integer type results in Integer (10..19,23..30) in ASN.1 and
Integer (10..30) in PER.

See X.691 annex B for full details on combining PER-visible and
non-PER-visible constraints.

encode recurses through an ASNType value until it gets to a
builtin type and then calls toPer. The final input to toPer is the
list of perVisible constraints of the layers of the type. The
first element in the list is the inner-most constraint.
\begin{code}
encode :: ASNType a -> a -> [ESS a] -> Either BitStream String
encode (BT t) v  cl    = toPer t v cl
encode (RT r) v  cl    = Left []
encode (ConsT t c) v cl
    = let b = getBT t
          pvc = perVisible b c
      in
        encode t v (pvc:cl)

-- need to deal with per-visible constraint list here.
-- generate effective root and effective extension here.
toPer :: ASNBuiltin a -> a -> [ESS a] -> Either BitStream String
toPer t@BOOLEAN x cl  = encodeBool t x
toPer t@INTEGER x cl  = encodeInt cl x


getBT :: ASNType a -> ASNType a
getBT b@(BT t) = b
getBT (ConsT t c) = getBT t
getBT (RT r)      = error "TO DO!!!"

perVisible :: ASNType a -> ESS a -> ESS a
perVisible (BT INTEGER) c = c



\end{code}
11 ENCODING THE BOOLEAN TYPE

\begin{code}

encodeBool :: ASNBuiltin Bool -> Bool -> Either BitStream String
encodeBool t True = Left [1]
encodeBool t _    = Left [0]

\end{code}

12 ENCODING THE INTEGER TYPE

-- If the type is unconstrained (has an empty constraint list) then enccodeUInt
-- is called.
-- If the type has at least one (serial) constraint then the root
-- constraint of the final constrained type is evaluated and used
-- to evaluate the extension. That is, when constraints are
-- serially applied only the extension of the final constraint
-- (the last in the list of constraints)
-- is retained and its effective constraint is dependent on the root of
-- its parent type.
-- The effective root constraint is also evaluated and this and
-- the effective extension are inputs of the function encInt.
-- An Either type value is returned to deal with illegal
-- constraints.

\begin{code}
encodeInt :: [ESS Int] -> Int -> Either BitStream String
encodeInt [] v
        = Left (encodeUInt v)
encodeInt c v
    = let
            lc = last c
            ic = init c
            parentRoot  = applyIntCons (Left (Just (minBound,maxBound))) ic
      in
            eitherTest parentRoot lc v

eitherTest :: IntConstraint -> ESS Int -> Int -> Either BitStream String
eitherTest (Right s) lc v = Right s
eitherTest pr@(Left c) lc v
    = let
            (effExt,b)  = applyExt pr lc
            effRoot     = evalC lc pr
      in
        encConsInt effRoot effExt b v
\end{code}

See Section 12 of X.691 (Encoding the Integer type).
\begin{code}

encConsInt :: IntConstraint -> IntConstraint -> Bool -> Int -> Either BitStream String
encConsInt _ (Right s) _ _ = Right s
encConsInt (Right s) _ _ _ = Right s
encConsInt (Left Nothing) (Left Nothing) True v
    = Right "Empty constraint"
encConsInt (Left (Just (l,u))) (Left Nothing) False v
    = if v >= l && v <= u
            then Left (encodeNNBIntBits (v-l,u-l))
            else Right "Value not in range"
encConsInt (Left (Just (l,u))) (Left Nothing) True v
    = if v >= l && v <= u
            then Left (0:encodeNNBIntBits (v-l,u-l))
            else Right "Value not in range"
encConsInt (Left Nothing) (Left (Just (l,u))) _ v
    = if v >= l && v <= u
            then Left (1:encodeUInt v)
            else Right "Value not in range"
encConsInt (Left (Just (l,u))) (Left (Just (el,eu))) _ v
    = if v >= el && v <= eu
            then Left (1:encodeUInt v)
            else if l == u && v == l
                then Left [0]
                else if v >= l && v <= u
                    then Left (0:encodeNNBIntBits (v-l,u-l))
                    else Right "Value out of range."

\end{code}

 10.6 Encoding as a normally small non-negative whole number

\begin{code}

encodeNSNNInt :: Int -> Int -> BitStream
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

encodeNNBIntBitsAux (_,0) = Nothing
encodeNNBIntBitsAux (0,w) = Just (0, (0, w `div` 2))
encodeNNBIntBitsAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

\end{code}

\begin{code}

encodeNNBIntBits :: (Int, Int) -> BitStream
encodeNNBIntBits
    = reverse . (map fromIntegral) . unfoldr encodeNNBIntBitsAux

\end{code}

 encodeNNBIntOctets encodes an integer in the minimum number of
 octets.

\begin{code}

encodeNNBIntOctets :: Int -> BitStream
encodeNNBIntOctets =
   reverse . (map fromIntegral) . flip (curry (unfoldr (uncurry g))) 8 where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))

\end{code}

 10.7 Encoding of a semi-constrained whole number. The integer
 is encoded in the minimum number of octets with an explicit
 length encoding.

\begin{code}

encodeSCInt :: Int -> Int -> BitStream
encodeSCInt v lb
    = encodeOctetsWithLength (encodeNNBIntOctets (v-lb))

\end{code}

 10.8 Encoding of an unconstrained integer. The integer is
 encoded as a 2's-complement-binary-integer with an explicit
 length encoding.

\begin{code}

encodeUInt :: Int -> BitStream
encodeUInt x = encodeOctetsWithLength (to2sComplement x)

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


lastLen :: Int -> [Int]
lastLen n
   | n <= 127       = 0:(encodeNNBIntBits (n, 127))
   | n < 16*(2^10)  = 1:0:(encodeNNBIntBits (n, (16*(2^10)-1)))

blockLen :: Int -> Int -> [Int]
blockLen x y = (1:1:(encodeNNBIntBits (x,y)))

\end{code}

encodeOctetsWithLength encodes a collection of octets with
unconstrained length. encodeBitsWithLength does the same except
for a collection of bits.

\begin{code}

encodeOctetsWithLength :: [Int] -> [Int]
encodeOctetsWithLength = encodeWithLength (concat . id) . groupBy 8


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

\section{Two's Complement Arithmetic}

10.4 Encoding as a 2's-complement-binary-integer is used when
encoding an integer with no lower bound (10.8) as in the final
case of encodeInt. The encoding of the integer is accompanied
by the encoding of its length using encodeOctetsWithLength
(10.8.3)

\begin{code}

to2sComplement :: Int -> BitStream
to2sComplement n
   | n >= 0 = 0:(h n)
   | otherwise = encodeNNBIntOctets (2^p + n)
   where
      p = length (h (-n-1)) + 1

g :: (Int, Int) -> Maybe (Int, (Int, Int))
g (0,0) = Nothing
g (0,p) = Just (0,(0,p-1))
g (n,0) = Just (n `rem` 2,(n `quot` 2,7))
g (n,p) = Just (n `rem` 2,(n `quot` 2,p-1))

h :: Int -> BitStream
h n = (reverse . map fromIntegral) (flip (curry (unfoldr g)) 7 n)

\end{code}

\begin{code}
-- X.680 G.4.2.3 states that extension additions are discarded if
-- a further constraint is subsequently serially applied.
-- Thus applyExt only requires the last constraint in the list
-- (the last in the serial application) and the root of the parent
-- type since values in extension additions can only be values that
-- are in the root of the parent type. The second element of the
-- returned pair indicates if the constraint is extensible (True) or
-- not (False).

applyExt :: IntConstraint -> ESS Int -> (IntConstraint, Bool)
applyExt rp (RE _)  = (Left Nothing, False)
applyExt rp (EXT _) = (Left Nothing, True)
applyExt rp (EXTWITH _ c)
                    = let ec = calcEC c
                      in
                        (applyExtWithRt rp ec, True)

-- Need to define calcEC (follow rules outlined in X.680 G.4.3.8)
-- and appExtWithRt
-- For Integer constraints, set operators are only applied to
-- non-extensible constraints (see 47.2 and 47.4 for definitions of
-- SingleValue and ValueRange constraints) and thus calcEC is simply
-- calcC. Thus G.4.3.8 can be ignored.

calcEC :: Constr Int -> IntConstraint
calcEC c = calcC c

-- applyExtWithRt is simply serialC (defined below) since it is
-- the serial application of the parent root and the extension of the
-- final constraint. Only values in the paernt root may appear in the
-- extension (see X.680 section G.4.2.3).
applyExtWithRt :: IntConstraint -> IntConstraint -> IntConstraint
applyExtWithRt a b = serialC a b

-- need to define encInt
encInt :: Maybe (Int,Int) -> Maybe (Int,Int) -> Bool -> Int -> BitStream
encInt r e b v = []

-- Need first input to host incremented constraint (due to serial constraints)
-- Need Either type to deal with legal and illegal constraints. An
-- illegal constraint (typically a mismatch between a parent type and
-- a constraint), will result in a string indicating the problem.
-- Need Maybe type to deal with empty constraint e.g. mutually exclusive intersection
-- As soon as one encounters an illegal constraint this is always
-- returned, and an empty constraint is only superceded by an illegal constraint.
-- Although an empty constraint could be viewed like an illegal
-- constraint (since it does not allow any legal values), this could
-- form either part of an extensible constraint whose overall effect
-- is legal.

type IntConstraint = Either (Maybe (Int,Int)) String

applyIntCons :: IntConstraint -> [ESS Int] -> IntConstraint
applyIntCons e@(Right s) _ = e
applyIntCons x [] = x
applyIntCons x (c:rs)
    = let c2 = evalC c x
      in applyIntCons c2 rs

evalC :: ESS Int -> IntConstraint -> IntConstraint
evalC (RE c) x
    = let c2 = calcC c
      in
        serialC x c2
-- Next case is the same as above since we are dealing with
-- extensions separately
evalC (EXT c) x
    = let c2 = calcC c
      in
        serialC x c2
-- and again!
evalC (EXTWITH c d) x
    = let c2 = calcC c
      in
        serialC x c2

-- See X.680 section G.4.2.3 for details on the serial application
-- of constraints. The second input is the new constraint whose
-- values must be bounded by the values in the first input. Thus
-- minBound in the second input matches the lower bound in the first
-- input and similarly for maxBound. Note that serialC takes two
-- Maybe type inputs since the illegal first input has already been
-- dealt with by applyIntCons. The second input cannot be illegal
-- since this is simply the (possible) set combination of atomic
-- constraints and involves no serial application of constraints.

serialC :: IntConstraint -> IntConstraint -> IntConstraint
serialC a@(Right s) _    = a
serialC _ b@(Right s)    = b
serialC f (Left Nothing) = Left Nothing
serialC a@(Left (Just (m,n))) b@(Left (Just (x,y)))
    = if x == (minBound :: Int) && y == (maxBound :: Int)
        then a
        else if y == (maxBound :: Int)
                then if x < m
                     then Right "Constraint and parent type mismatch."
                     else Left (Just (x,n))
             else if x == (minBound :: Int)
                     then if y > n
                            then Right "Constraint and parent type mismatch."
                            else Left (Just (m,y))
                  else if x < m || y > n
                      then Right "Constraint and parent type mismatch."
                       else interC a b

calcC :: Constr Int -> IntConstraint
calcC (UNION u) = calcU u
calcC (ALL e)   = exceptC (Left (Just (minBound,maxBound))) (calcEx e)

-- Need to define unionC which returns the union of two
-- constraints
calcU :: Union Int -> IntConstraint
calcU (IC i )  = calcI i
calcU (UC u i) = let x = calcU u
                     y = calcI i
                 in unionC x y


unionC :: IntConstraint -> IntConstraint -> IntConstraint
unionC a@(Right s) _      = a
unionC _ b@(Right s)      = b
unionC (Left Nothing) y   = y
unionC x (Left Nothing)   = x
unionC (Left (Just (m,n))) (Left (Just (x,y)))
    = if m < x
        then unionC' (Just (m,n)) (Just (x,y))
        else unionC' (Just (x,y)) (Just (m,n))

unionC' a@(Just (m,n)) b@(Just (x,y))
    = if y > n then Left (Just (m,y))
        else (Left a)


calcI :: IntCon Int -> IntConstraint
calcI (INTER i e) = let x = calcI i
                        y = calcA e
                    in interC x y
calcI (ATOM a)    = calcA a

interC :: IntConstraint -> IntConstraint -> IntConstraint
interC a@(Right s) _      = a
interC _ b@(Right s)      = b
interC (Left Nothing) _   = (Left Nothing)
interC _ (Left Nothing)   = (Left Nothing)
interC (Left (Just (m,n))) (Left (Just (x,y)))
    = if m < x
        then interC' (Just (m,n)) (Just (x,y))
        else interC' (Just (x,y)) (Just (m,n))

interC' a@(Just (m,n)) b@(Just (x,y))
    = if x > n then (Left Nothing)
        else if y <= n
            then (Left b)
                else (Left (Just (x,n)))

calcA :: IE Int -> IntConstraint
calcA (E e )     = calcE e
calcA (Exc e ex) = let x = calcE e
                       y = calcEx ex
                   in exceptC x y

-- Note that the resulting constraint is always a contiguous set.
exceptC :: IntConstraint -> IntConstraint -> IntConstraint
exceptC a@(Right s) _      = a
exceptC _ b@(Right s)      = b
exceptC a@(Left Nothing) _ = a
exceptC x (Left Nothing) = x
exceptC a@(Left (Just (m,n))) b@(Left (Just (x,y)))
    = if x > n || y < m then a
        else if x > m && y < n
            then a
            else if x <= m && y >= n
                    then (Left Nothing)
                    else (Left (Just (m,x-1)))

-- Need processCT to process the constraint implications of type
-- inclusion.
-- NOTE: Need to deal with illegal constraints resulting from
-- processCT
calcE :: Elem Int -> IntConstraint
calcE (S (SV i))    = Left (Just (i,i))
calcE (C (Inc t))   = processCT t []
calcE (V (R (l,u))) = Left (Just (l,u))



calcEx :: Excl Int -> IntConstraint
calcEx (EXCEPT e) = calcE e

-- Need to define reference case which requires derefencing.
-- This function is similar to the encode function in that it
-- needs to produce the effective constraint for the included type.
processCT :: ASNType Int -> [ESS Int] -> IntConstraint
processCT (BT INTEGER) cl = applyIntCons (Left (Just (minBound,maxBound))) cl
processCT (RT r) cl       = error "Need to do"
processCT (ConsT t c) cl  = let pvc = perVisible t c
                            in
                            processCT t (pvc:cl)


\end{code}

\begin{code}

bitPutify :: BitStream -> BP.BitPut
bitPutify = mapM_ (BP.putNBits 1)

decodeUInt :: (MonadError [Char] (t1 BG.BitGet), MonadTrans t1) => t1 BG.BitGet Integer
decodeUInt =
   do o <- octets
      return (from2sComplement o)
   where
      chunkBy8 = let compose = (.).(.) in lift `compose` (flip (const (BG.getLeftByteString . fromIntegral . (*8))))
      octets   = decodeLargeLengthDeterminant chunkBy8 undefined

decodeLargeLengthDeterminant f t =
   do p <- lift BG.getBit
      if (not p) 
         then
            do j <- lift $ BG.getLeftByteString 7
               let l = fromNonNeg 7 j
               f l t
         else
            do q <- lift BG.getBit
               if (not q)
                  then
                     do k <- lift $ BG.getLeftByteString 14
                        let m = fromNonNeg 14 k
                        f m t
                  else
                     do n <- lift $ BG.getLeftByteString 6
                        let fragSize = fromNonNeg 6 n
                        if fragSize <= 0 || fragSize > 4
                           then throwError (fragError ++ show fragSize)
                           else do frag <- f (fragSize * n16k) t
                                   rest <- decodeLargeLengthDeterminant f t
                                   return (B.append frag rest)
                        where
                           fragError = "Unable to decode with fragment size of "

n16k = 16*(2^10)

fromNonNeg r x = 
   sum (zipWith (*) (map fromIntegral ys) zs)
   where
      s = (-r) `mod` bSize
      bSize = bitSize (head ys)
      ys = reverse (B.unpack (rightShift s x))
      zs = map ((2^bSize)^) [0..genericLength ys]

from2sComplement a = x
   where
      l = fromIntegral (B.length a)
      b = l*8 - 1 
      (z:zs) = B.unpack a
      t = (fromIntegral (shiftR (0x80 .&. z) 7)) * 2^b
      powersOf256 = 1:(map (256*) powersOf256)
      r = zipWith (*) powersOf256 (map fromIntegral (reverse ((0x7f .&. z):zs)))
      x = -t + (sum r)

\end{code}

\begin{code}

decConsInt rootConstraint extensionConstraint isExtension value =
   if (not isExtension)
      then
         do mr <- rootConstraint -- If we get an error (Right for now) then this will percolate upwards
            return (encodeWithRootConstraint mr)
      else
         undefined
   where
      encodeWithRootConstraint mr =
         do (l,u) <- mr -- If there is no constraint then Nothing will percolate upwards
            let range = u - l + 1
                n     = genericLength (encodeNNBIntBits ((u-l),range-1))
            if range <= 1
               then 
                  return l
               else
                  do j <- BG.getLeftByteString n
                     return (l + (fromNonNeg n j))

encodeWithRootConstraint mr =
   do (l,u) <- mr -- If there is no constraint then Nothing will percolate upwards
      let range = u - l + 1
          n     = genericLength (encodeNNBIntBits ((u-l),range-1))
      if range <= 1
         then 
            return l
         else
            do j <- BG.getLeftByteString n
               return (l + (fromNonNeg n j))

swap :: (Functor m, Monad m) => Either String (m a) -> m (Either String a)
swap (Left s) = return (Left s)
swap (Right x) = fmap Right x

instance F.Foldable (Either String) where
   foldMap f (Left s)  = mempty
   foldMap f (Right x) = f x

instance T.Traversable (Either String) where
   traverse f (Left s)  = pure (Left s)
   traverse f (Right x) = Right <$> f x

instance Functor BG.BitGet -- kludge

bar :: Either String (Int,Int) -> BG.BitGet (Either String Int)
bar x =
   case x of
      Left err -> return (Left err)
      Right (x,y) -> do b <- BG.getBit
                        return (Right (fromEnum b))

boo :: Either String (Int,Int) -> Either String (BG.BitGet Int)
boo x =
   case x of
      Left err -> Left err
      Right (u,v) -> Right (do b <- BG.getBit; return (fromEnum b))
      
buz :: Either String (Int,Int) -> Either String (BG.BitGet Int)
buz x =
   do (u,v) <- x
      return (do b <- BG.getBit; return (fromEnum b))

bux :: Either String (Int,Int) -> Either String (BG.BitGet Int)
bux x =
   do (u,v) <- x
      return (f u v)
   where
      f u v =
         do b <- BG.getBit
            if b
               then return u
               else return v

option1 = swap . bux

option2 = T.sequence . bux

\end{code}

\end{document}
