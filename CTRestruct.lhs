\documentclass{article}
%include polycode.fmt

\newcommand{\bottom}{\perp}

\begin{document}

\section{Introduction}

ASN.1 --- Abstract Syntax Notation --- is a large and complex specification for communicating abstract data definitions
together with several concrete encodings. It is widely used, for example, to describe digital certificates and to 
third generation mobile telephony~\cite{3gpp.25.413} and~\cite{ACARS}.


The encoding is for UNALIGNED PER

\begin{code}
{-# OPTIONS_GHC -XMultiParamTypeClasses -XGADTs -XTypeOperators -XEmptyDataDecls -XFlexibleInstances -XFlexibleContexts #-}

module CTRestruct where

import qualified Data.Map as Map
import Data.List hiding (groupBy)
import Data.Bits
import Data.Char
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity
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

import qualified LatticeMod as L
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

data Sz a = SizeConstraint a => SC (ESS Integer)

data PA a = PermittedAlphabet a => FR (ESS a)

--IS to be completed for multiple type constraints
data IS a = InnerType a => WC (ESS a) | WCS

-- Type constraint (constraining an open type) to be done (47.6)
-- Pattern constraint to be done.
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
   INTEGER         :: ASNBuiltin Integer
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

-- Need a new type to represent a VisibleString (any restricted character string type) when
-- developing an effective permitted alphabet constraint.

data L.RS t => PAResString t = PE t
    deriving (Show, Eq)
instance L.RS a => L.RS (PAResString a) where
    getString (PE s) = L.getString s
    putString s = PE (L.putString s)

\end{code}

Type Classes which make explicit the (not necessarily PER-visible) subtypes associated with the ASN.1 types.

See X.680 (07/2002) Section 47.1 Table 9

RST is a type class for the restricted character string types.

\begin{code}

class MonadError [Char] m => RST m a where
    conE :: (Eq a, L.Lattice a, L.RS a, L.Lattice (m (L.ExtResStringConstraint a)))
        => Elem a -> Bool -> m (L.ExtResStringConstraint a)

instance RST (Either [Char]) VisibleString where
    conE = lResConE
-- instance RST a => RST (Either [Char]) (PAResString a) where
instance (RST (Either [Char]) a, Eq a, L.Lattice a, L.RS a) => RST (Either [Char]) (PAResString a) where
    conE = lPaConE


class SingleValue a

instance SingleValue BitString
instance SingleValue IA5String
instance SingleValue PrintableString
instance SingleValue Int
instance L.RS a => SingleValue (PAResString a)

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
instance ValueRange Integer -- Another example of the Int / Integer problem


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

lEncode :: ASNType a -> a -> [ESS a] -> Either String BP.BitPut
lEncode (BT t) v cl =
   lToPer t v cl
lEncode (RT _) _ _ =
   error "RT"
lEncode (ConsT t c) v cl = lEncode t v (c:cl)

\end{code}

need to deal with per-visible constraint list here.
generate effective root and effective extension here.

\begin{code}

lToPer :: (L.Lattice (m L.IntegerConstraint),
           L.Lattice (m (L.ExtResStringConstraint VisibleString)),
           L.Lattice (m (L.ResStringConstraint VisibleString)),
           RST m VisibleString,
           MonadError [Char] m) => ASNBuiltin a -> a
           -> [ESS a] -> m BP.BitPut
lToPer t@INTEGER x cl       = lEncodeInt cl x
lToPer t@VISIBLESTRING x cl = lEncodeVisString cl x

\end{code}

-- GENERATION OF EFFECTIVE STRING CONSTRAINT

-- resEffCons takes a restricted string constraint and returns either a pair
-- of effective constraints or a message indicating that the constraint is
-- not PER-visible. The pair includes the
-- effective size constraint and the effective permitted alphabet
-- constraint. The evaluation takes account of the effect of set
-- operators and extensibility. Note that extensible size and
-- permitted alphabet constraints may be combined using set operators
-- which is not the case for an Integer value range constraint.
-- The return type is a pair of ResStringContraint values - the first for
-- the root constraint and the second for the extension constraint -
-- paired with a boolean value that indicates whether an extension is
-- expected (hence a bit prefix in the encoding) or not.
-- ResStringConstraint is a phantom type (to allow for the different restricted string types)
-- encompassing the (size,permittedAlphabet) constraint pair.
-- Maybe types are used to deal with the case of empty constraints
-- (such as an intersection of non-overlapping size constraints) or
-- non-existent extensions.

serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
--- effective constraint (if it exists).

{- NOTE WE WANT THE TYPE TO BE MORE GENERAL e.g. replaced VisibleString with RS a => a -}

serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

\begin{code}

lSerialResEffCons :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)),
                      L.Lattice (m (L.ResStringConstraint a)))
                      => m (L.ExtResStringConstraint a) -> [ESS a]
                          -> m (L.ExtResStringConstraint a)
lSerialResEffCons m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = lSerialApplyLast esrc c
                        foobar1 (f:r) = lSerialResEffCons (lSerialApply esrc f) r
                    foobar1 ls
        catchError foobar (\err -> throwError err)

lSerialApply :: (MonadError [Char] m, L.RS a, RST m a, L.Lattice (m (L.ExtResStringConstraint a)),
                    Eq a, L.Lattice a, L.Lattice (m (L.ResStringConstraint a)))
                => L.ExtResStringConstraint a -> ESS a -> m (L.ExtResStringConstraint a)
lSerialApply ersc c = lEitherApply ersc (lResEffCons c)

\end{code}

\begin{code}

lEitherApply :: (MonadError [Char] m, L.RS a, RST m a,L.Lattice (m (L.ResStringConstraint a)),
                 Eq a, L.Lattice a, L.Lattice (m (L.ExtResStringConstraint a)))
                => L.ExtResStringConstraint a -> m (L.ExtResStringConstraint a)
                                    -> m (L.ExtResStringConstraint a)
lEitherApply (L.ExtResStringConstraint rc1 _ _) m
    = do
        let foobar
                = do x <- m
                     let rc2 = L.getRC x
                         foobar1
                            = if lValidResCon rc1 rc2
                                 then return (L.ExtResStringConstraint (lUpdateResCon rc1 rc2) L.top False)
                                 else throwError "Parent type and constraint mismatch"
                     foobar1
        catchError foobar (\err -> throwError err)

lValidResCon :: (L.Lattice a, L.RS a, Eq a) => L.ResStringConstraint a -> L.ResStringConstraint a -> Bool
lValidResCon (L.ResStringConstraint s1 p1) (L.ResStringConstraint s2 p2)
    = lValidSize s1 s2 && lValidPA p1 p2

lValidSize :: L.IntegerConstraint -> L.IntegerConstraint -> Bool
lValidSize x y
    = if x == L.top || y == L.top
        then True
        else
            let l1 = L.getLower x
                u1 = L.getUpper x
                l2 = L.getLower y
                u2 = L.getUpper y
            in
                l2 == minBound && u2 <= u1 || u2 == maxBound && l2 >= l1 || l1 <= l2 && u1 >= u2

lValidPA :: (L.Lattice a, L.RS a, Eq a) => a -> a -> Bool
lValidPA x y
    = if x == L.top || y == L.top
        then True
        else and (map (flip elem (L.getString x)) (L.getString y))

lUpdateResCon :: (L.Lattice a, L.RS a, Eq a) => L.ResStringConstraint a -> L.ResStringConstraint a
                           -> L.ResStringConstraint a
lUpdateResCon (L.ResStringConstraint s1 p1) (L.ResStringConstraint s2 p2)
     = L.ResStringConstraint (lUpdateSize s1 s2) (lUpdatePA p1 p2)

lUpdateSize :: L.IntegerConstraint -> L.IntegerConstraint -> L.IntegerConstraint
lUpdateSize x y
    = if x == L.bottom || y == L.bottom
        then L.bottom
        else if x == L.top
                then y
                else if y == L.top
                        then x
                        else
                            let l1 = L.getLower x
                                u1 = L.getUpper x
                                l2 = L.getLower y
                                u2 = L.getUpper y
                            in if l2 == minBound && u1 == u2
                                then x
                                else if u2 == maxBound
                                        then L.IntegerConstraint l2 u1
                                        else y

lUpdatePA :: (L.Lattice a, L.RS a, Eq a) => a -> a -> a
lUpdatePA x y
    = if x == L.bottom || y == L.bottom
        then L.bottom
        else y

lSerialApplyLast :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                     L.Lattice (m (L.ResStringConstraint a)),
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => L.ExtResStringConstraint a -> ESS a
                          -> m (L.ExtResStringConstraint a)
lSerialApplyLast x c = lLastApply x (lResEffCons c)

lLastApply :: (MonadError [Char] m, L.RS a, RST m a, Eq a,
               L.Lattice a, L.Lattice (m (L.ResStringConstraint a)),
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => L.ExtResStringConstraint a -> m (L.ExtResStringConstraint a)
                          -> m (L.ExtResStringConstraint a)
lLastApply x@(L.ExtResStringConstraint r1 _ _) m
    = do
         let foobar
                 = do
                    (L.ExtResStringConstraint r2 e2 _) <- m
                    let foobar1
                         | not (L.extensible x) = lEitherApply x m
                         | lValidResCon r1 r2 && lValidResCon r1 e2
                            = return (L.ExtResStringConstraint (lUpdateResCon r1 r2)
                                                    (lUpdateResCon r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
         catchError foobar (\err -> throwError err)

\end{code}

resEffCons generates the effective constraint of a restricted
type constraint.

\begin{code}

lResEffCons :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => ESS a -> m (L.ExtResStringConstraint a)
lResEffCons (RE c)         = lResCon c False
lResEffCons (EXT c)        = lResCon c True
lResEffCons (EXTWITH c e)  = lExtendResC (lResCon c False) (lResCon e False)

\end{code}

resCon processes constraints. Its second input indicates if the
type is extensible.

\begin{code}

lResCon :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => Constr a -> Bool -> m (L.ExtResStringConstraint a)
lResCon (UNION u) b        = lResConU u b
lResCon (ALL (EXCEPT e)) b = lResExceptAll L.top (conE e b)

\end{code}

extendresC implements the extension operator (...) on visiblestring
constraints.
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)

\begin{code}

lExtendResC :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => m (L.ExtResStringConstraint a) -> m (L.ExtResStringConstraint a)
                         -> m (L.ExtResStringConstraint a)
lExtendResC m n
    = do
        let foobar
                = do
                    x@(L.ExtResStringConstraint r1 e1 _) <- m
                    y@(L.ExtResStringConstraint r2 e2 _) <- n
                    let foobar1
                            | not (L.extensible x) && not (L.extensible y)
                                = return (L.ExtResStringConstraint r1 (L.exceptRSC r2 r1) True)
                            | L.extensible x && not (L.extensible y)
                                = return (L.ExtResStringConstraint r1 (L.exceptRSC (e1 `L.ljoin` r2) r1) True)
                            | not (L.extensible x) && L.extensible y
                                = return (L.ExtResStringConstraint r1 (L.exceptRSC (r2 `L.ljoin` e2) r1) True)
                            | L.extensible x && L.extensible y
                                = return (L.ExtResStringConstraint r1
                                            (L.exceptRSC (e1 `L.ljoin` (r2 `L.ljoin` e2)) r1) True)
                    foobar1
        catchError foobar (\err -> throwError "Invisible")

\end{code}

resExceptAll has to deal with the various potential universal
sets which are dependent on the nature of the excepted constraint.
Note: The resulting constraint is non-extensible (see X.680
G.4.3.8)

\begin{code}

lResExceptAll :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => (L.ResStringConstraint a) -> m (L.ExtResStringConstraint a)
                         -> m (L.ExtResStringConstraint a)
lResExceptAll t m
    = do
         let foobar
                = do
                    ersc <- m
                    let rc = L.getRC ersc
                        emptyConstraint = rc == L.bottom
                        foobar1
                            | emptyConstraint = return (L.ExtResStringConstraint t L.top False)
                            | otherwise = return (L.ExtResStringConstraint (L.exceptRSC L.top rc) L.top False)
                    foobar1
         catchError foobar (\err -> throwError "Invisible")

lResConU :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => Union a -> Bool -> m (L.ExtResStringConstraint a)
lResConU (IC i) b  = lResConI i b
lResConU (UC u i) b = lUnionResC (lResConI i b) (lResConU u False)

\end{code}

unionRes returns the union of two pairs of constraints. Note
that the union of a size constraint (and no permitted alphabet constraint)
and vice versa result in no constraint.
sizeUnion and paUnion union size and permitted alphabet constraints respectively.

unionresC implements the union operator on visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680) Note that a union of a size constraint and a permitted
alphabet constraint is an unconstrained type.

\begin{code}

lUnionResC :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => m (L.ExtResStringConstraint a) -> m (L.ExtResStringConstraint a)
                         -> m (L.ExtResStringConstraint a)
lUnionResC m n
    = do
        let foobar
             = do
                c1 <- m
                c2 <- n
                let r1 = L.getRC c1
                    e1 = L.getEC c1
                    r2 = L.getRC c2
                    e2 = L.getEC c2
                    foobar1
                        | not (L.extensible c1) && not (L.extensible c2)
                             = return (L.ExtResStringConstraint (r1 `L.ljoin` r2) L.top False)
                        | not (L.extensible c1)
                             = return (L.ExtResStringConstraint (r1 `L.ljoin` r2) e2 True)
                        | L.extensible c1 && not (L.extensible c2)
                             = return (L.ExtResStringConstraint (r1 `L.ljoin` r2) e1 True)
                        | otherwise
                             = return (L.ExtResStringConstraint (r1 `L.ljoin` r2)
                                       (L.exceptRSC ((r1 `L.ljoin` e1) `L.ljoin` (r2 `L.ljoin` e2))
                                                  (r1 `L.ljoin` r2)) True)
                foobar1
        catchError foobar (\err -> throwError "Invisible")

\end{code}

resConI deals with the intersection of visiblestring constraints

\begin{code}

lResConI :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                 L.Lattice (m (L.ExtResStringConstraint a)))
                      => IntCon a -> Bool -> m (L.ExtResStringConstraint a)
lResConI (INTER i e) b = lInterResC (lResConA e b) (lResConI i False)
lResConI (ATOM e) b = lResConA e b

\end{code}

interResC implements the intersection of visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lInterResC :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => m (L.ExtResStringConstraint a) -> m (L.ExtResStringConstraint a)
                         -> m (L.ExtResStringConstraint a)
lInterResC m n
    = do
         let foobar1 x
                 = catchError (do c2 <- n
                                  foobar2 x c2)
                              (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = L.getRC c1
                        e1 = L.getEC c1
                        r2 = L.getRC c2
                        e2 = L.getEC c2
                        foobar3
                            | not (L.extensible c1) && not (L.extensible c2)
                                 = return (L.ExtResStringConstraint (r1 `L.meet` r2) L.top False)
                            | not (L.extensible c1)
                                 = return (L.ExtResStringConstraint (r1 `L.meet` r2) (r1 `L.meet` e2) True)
                            | L.extensible c1 && not (L.extensible c2)
                                 = return (L.ExtResStringConstraint (r1 `L.meet` r2) (r2 `L.meet` e1)  True)
                            | otherwise
                                 = return (L.ExtResStringConstraint (r1 `L.meet` r2) (L.exceptRSC ((r1 `L.ljoin` e1)
                                        `L.meet` (r2 `L.ljoin` e2)) (r1 `L.meet` r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> n)
         foobar

\end{code}

resConA deals with atomic (including except) constraints

\begin{code}

lResConA :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                 L.Lattice (m (L.ExtResStringConstraint a)))
                      => IE a -> Bool -> m (L.ExtResStringConstraint a)
lResConA (E e) b = conE e b
lResConA (Exc e (EXCEPT ex)) b
                = lExceptResC (conE e b) (conE ex False)

\end{code}

resExcept implements the set difference operator applied to
visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lExceptResC :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
                      L.Lattice (m (L.ExtResStringConstraint a)))
                      => m (L.ExtResStringConstraint a) -> m (L.ExtResStringConstraint a)
                         -> m (L.ExtResStringConstraint a)
lExceptResC m n
    = do
         let foobar1 x
                 = catchError (do c2 <- n
                                  foobar2 x c2)
                              (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = L.getRC c1
                        e1 = L.getEC c1
                        r2 = L.getRC c2
                        e2 = L.getEC c2
                        foobar3
                            | not (L.extensible c1)
                                = return (L.ExtResStringConstraint (L.exceptRSC r1 r2) L.top False)
                            | L.extensible c1 && not (L.extensible c2)
                                 = return (L.ExtResStringConstraint (L.exceptRSC r1 r2)
                                            (L.exceptRSC (L.exceptRSC r1 e2) (L.exceptRSC r1 r2)) True)
                            | otherwise
                                 = return (L.ExtResStringConstraint (L.exceptRSC r1 r2)
                                            (L.exceptRSC (L.exceptRSC r1 (r2 `L.ljoin` e2))
                                                       (L.exceptRSC r1 r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> throwError "Invisible")
         foobar

\end{code}

resConE deals with the various visiblestring constraints
Note that a permitted alphabet constraint uses value range
constraint(s) and that extensible permitted alphabet
constraints are not per-visible.
The first case (size-constraint) we can make use of the
functions that create an effective Integer constraint. We
cannot use evalC since it includes serial application of
constraints.

\begin{code}

lResConE :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
            L.Lattice (m (L.ExtResStringConstraint a)),
            L.Lattice (m L.IntegerConstraint))
             => Elem a -> Bool -> m (L.ExtResStringConstraint a)
lResConE (SZ (SC v)) b            = lEffResSize v b
lResConE (P (FR (EXT _))) b       = throwError "Invisible!"
lResConE (P (FR (EXTWITH _ _))) b = throwError "Invisible!"
lResConE (P (FR (RE p)))  b       = lResEffCons (RE p)
lResConE (C (Inc c)) b            = throwError "TO BE DONE!!!"
lResConE (S (SV v))  b            = throwError "Invisible!"

\end{code}

paConE deals with the various visiblestring constraints
Note that a permitted alphabet constraint uses value range
constraint(s) and that extensible permitted alphabet
constraints are not per-visible.
The first case (size-constraint) we can make use of the
functions that create an effective Integer constraint. We
cannot use evalC since it includes serial application of
constraints.

\begin{code}

lPaConE :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,
            L.Lattice (m (L.ExtResStringConstraint a)))
                => Elem (PAResString a) -> Bool ->
                            m (L.ExtResStringConstraint (PAResString a))
lPaConE (V (R (l,u))) b
    = let ls = L.getString l
          us = L.getString u
          rs = [head ls..head us]
        in
            return (L.ExtResStringConstraint (L.ResStringConstraint L.top (L.putString rs))
                        (L.ResStringConstraint L.top (PE L.top)) b)
lPaConE (C (Inc c)) b = throwError "TO DO!"
lPaConE (S (SV (PE v))) b
   = return (L.ExtResStringConstraint (L.ResStringConstraint L.top (PE v))
                                      (L.ResStringConstraint L.top (PE L.top)) b)

lEffResSize :: (MonadError [Char] m, L.RS a, RST m a, Eq a, L.Lattice a,L.Lattice (m L.IntegerConstraint),
                      L.Lattice (m (L.ExtResStringConstraint a)))
                => ESS Integer -> Bool -> m (L.ExtResStringConstraint a)
lEffResSize (RE c) b
    = do ec <- lCalcC c
         return (L.ExtResStringConstraint (L.ResStringConstraint ec L.top) L.top b)
lEffResSize (EXT c) b
    = do ec <- lCalcC c
         return (L.ExtResStringConstraint (L.ResStringConstraint ec L.top) L.top True)
lEffResSize (EXTWITH c d) b
    = do r <- lCalcC c
         e <- lCalcC d
         return (L.ExtResStringConstraint (L.ResStringConstraint r L.top)
                                        (L.ResStringConstraint e L.top)  True)

\end{code}

END OF EFFECTIVE RSC GENERATION

\section{ENCODING THE BOOLEAN TYPE (11)}

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
{-
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
-}
myEncodeUInt = bitPutify . encodeUInt . fromIntegral -- Another Int bug waiting to happen


lEncodeInt :: (L.Lattice (m L.IntegerConstraint), MonadError [Char] m) => [ESS Integer]
                -> Integer -> m BP.BitPut
lEncodeInt [] v = return (myEncodeUInt v)
lEncodeInt cs v =
   lEitherTest parentRoot lc v
   where
      lc         = last cs
      ic         = init cs
      parentRoot = lApplyIntCons L.top ic

lEitherTest :: (MonadError String m, L.Lattice (m L.IntegerConstraint)) =>
               m L.IntegerConstraint -> ESS Integer -> Integer -> m BP.BitPut
lEitherTest pr lc v =
   lEncConsInt effRoot effExt b v
   where
      (effExt,b) = lApplyExt pr lc
      effRoot    = lEvalC lc pr

\end{code}

See Section 12 of X.691 (Encoding the Integer type).
\begin{code}
{-
encConsInt :: IntConstraint -> IntConstraint -> Bool -> Int -> Either BitStream String
encConsInt rootCon extCon extensible v
    = if (not extensible)
        then encNonExtConsInt rootCon v
        else encExtConsInt rootCon extCon v

encNonExtConsInt :: IntConstraint -> Int -> Either BitStream String
encNonExtConsInt (Right s) _      = Right s
encNonExtConsInt (Left Nothing) _ = Right "Empty Constraint"
encNonExtConsInt (Left (Just (l,u))) v
    = if v >= l && v <= u
            then if l == minBound
                then Left (encodeUInt v)
                else if u == maxBound
                     then Left (encodeSCInt v l)
                     else Left (encodeNNBIntBits (v-l,u-l))
            else Right "Value not in range"

encExtConsInt :: IntConstraint -> IntConstraint -> Int -> Either BitStream String
encExtConsInt _ (Right s) _ = Right s
encExtConsInt (Right s) _ _ = Right s
encExtConsInt (Left Nothing) (Left Nothing) v
    = Right "Empty constraint"
encExtConsInt (Left (Just (l,u))) (Left Nothing) v
    = if v >= l && v <= u
            then if l == minBound
                then Left (0:encodeUInt v)
                else if u == maxBound
                     then Left (0:encodeSCInt v l)
                     else Left (0:encodeNNBIntBits (v-l,u-l))
            else Right "Value not in range"
encExtConsInt (Left Nothing) (Left (Just (l,u))) v
    = if v >= l && v <= u
            then Left (1:encodeUInt v)
            else Right "Value not in range"
encExtConsInt (Left (Just (l,u))) (Left (Just (el,eu))) v
    = if l == u && v == l
           then Left [0]
           else if v >= l && v <= u
                    then if l == minBound
                            then Left (0:encodeUInt v)
                            else if u == maxBound
                                    then Left (0:encodeSCInt v l)
                                    else Left (0:encodeNNBIntBits (v-l,u-l))
                   else
                        if v >= el && v <= eu
                             then Left (1:encodeUInt v)
                             else Right "Value out of range."

-}

lEncConsInt :: (MonadError [Char] m) => m L.IntegerConstraint -> m L.IntegerConstraint -> Bool
                                        -> Integer -> m BP.BitPut
lEncConsInt rootCon extCon extensible v
    = if (not extensible)
        then lEncNonExtConsInt rootCon v
        else lEncExtConsInt rootCon extCon v


\end{code}

\section{Dan: read this as an example of our paper for a formal executable specification of PER}

For the purpose of encoding in PER, we can classify an INTEGER type as
constrained, semi-constrained or unconstrained.

\begin{code}

data IntegerConstraintType =
   Constrained     |
   SemiConstrained |
   UnConstrained

\end{code}

First, the type signature tells us that we are using constraints which are \lq\lq lifted\rq\rq.
The type constructor $m$ takes a type $a$ and constructs a new type $m a$, a \lq\lq lifting\rq\rq
of the base type. This monad allows us to handle invalid serial application of constraints without
cluttering up the specification with \lq\lq plumbing\rq\rq. The Haskell constraint to the left of the $\Rightarrow$ tells us that the
type constructor is a monad with extra structure. This extra structure allows us to signal an
error using {\tt throwError}, for example in the case of values which are not in range given by the constraints and then
handle it using {\tt catchError}.

We can now read off the specificiation:

\begin{enumerate}

\item
Extract the values from the monad.

\item
If there is a root constraint and an extension constraint and the value
is consistent with the root constraint then \ldots

\item
If there is a root constraint and an extension constraint and the value
is consistent with the extension constraint then \ldots

\end{enumerate}

\begin{code}

lEncExtConsInt :: (MonadError [Char] m) => m L.IntegerConstraint -> m L.IntegerConstraint -> Integer
                                           -> m BP.BitPut
lEncExtConsInt mrc mec v =
   do rc <- mrc
      ec <- mec
      let isNonEmptyEC           = ec /= L.bottom
          isNonEmptyRC           = rc /= L.bottom
          emptyConstraint        = (not isNonEmptyRC) && (not isNonEmptyEC)
          inRange x              = (L.V v) >= (L.lower x) &&  (L.V v) <= (L.upper x)
          unconstrained x        = (L.lower x) == minBound
          semiconstrained x      = (L.upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          rootLower              = let (L.V y) = L.lower rc in y
          rootUpper              = let (L.V y) = L.upper rc in y
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rc
                  = return $ do BP.putNBits 1 (0::Int)
                                case constraintType rc of
                                   UnConstrained ->
                                      bitPutify (encodeUInt (fromIntegral v))
                                   SemiConstrained ->
                                      bitPutify (encodeSCInt (fromIntegral v) rootLower)
                                   Constrained ->
                                      bitPutify (encodeNNBIntBits (fromIntegral (v - rootLower), fromIntegral (rootUpper - rootLower)))
             | isNonEmptyEC &&
               inRange ec
                  = return $ do BP.putNBits 1 (1::Int)
                                bitPutify (encodeUInt (fromIntegral v))

             | otherwise
                  = throwError "Value out of range"
      foobar

lEncNonExtConsInt :: (MonadError [Char] m) => m L.IntegerConstraint -> Integer -> m BP.BitPut
lEncNonExtConsInt mrc v =
   do rc <- mrc
      let isNonEmptyRC           = rc /= L.bottom
          emptyConstraint        = not isNonEmptyRC
          inRange x              = (L.V v) >= (L.lower x) &&  (L.V v) <= (L.upper x)
          unconstrained x        = (L.lower x) == minBound
          semiconstrained x      = (L.upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          rootLower              = let (L.V y) = L.lower rc in y
          rootUpper              = let (L.V y) = L.upper rc in y
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rc
                  = return $ do
                       case constraintType rc of
                                   UnConstrained ->
                                      bitPutify (encodeUInt (fromIntegral v))
                                   SemiConstrained ->
                                      bitPutify (encodeSCInt (fromIntegral v) rootLower)
                                   Constrained ->
                                      bitPutify (encodeNNBIntBits (fromIntegral (v - rootLower), fromIntegral (rootUpper - rootLower)))
             | otherwise
                  = throwError "Value out of range"
      foobar
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

\end{code}

 10.8 Encoding of an unconstrained integer. The integer is
 encoded as a 2's-complement-binary-integer with an explicit
 length encoding.

\begin{code}

encodeUInt :: Integer -> BitStream
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

\begin{code}
-- X.680 G.4.2.3 states that extension additions are discarded if
-- a further constraint is subsequently serially applied.
-- Thus applyExt only requires the last constraint in the list
-- (the last in the serial application) and the root of the parent
-- type since values in extension additions can only be values that
-- are in the root of the parent type. The second element of the
-- returned pair indicates if the constraint is extensible (True) or
-- not (False).
{-
applyExt :: IntConstraint -> ESS Int -> (IntConstraint, Bool)
applyExt rp (RE _)  = (Left Nothing, False)
applyExt rp (EXT _) = (Left Nothing, True)
applyExt rp (EXTWITH _ c)
                    = let ec = calcEC c
                      in
                        (applyExtWithRt rp ec, True)
-}
lApplyExt :: (L.Lattice (m L.IntegerConstraint), MonadError String m) =>
             m L.IntegerConstraint -> ESS Integer -> (m L.IntegerConstraint, Bool)
lApplyExt rp (RE _)  = (L.bottom, False)
lApplyExt rp (EXT _) = (L.bottom, False)
lApplyExt rp (EXTWITH _ c) = (lApplyExtWithRt rp (lCalcEC c), True)

-- Need to define calcEC (follow rules outlined in X.680 G.4.3.8)
-- and appExtWithRt
-- For Integer constraints, set operators are only applied to
-- non-extensible constraints (see 47.2 and 47.4 for definitions of
-- SingleValue and ValueRange constraints) and thus calcEC is simply
-- calcC. Thus G.4.3.8 can be ignored.
{-
calcEC :: Constr Int -> IntConstraint
calcEC c = calcC c
-}
lCalcEC :: (L.Lattice (m L.IntegerConstraint), MonadError String m) =>
           Constr Integer -> m L.IntegerConstraint
lCalcEC c = lCalcC c

-- applyExtWithRt is simply serialC (defined below) since it is
-- the serial application of the parent root and the extension of the
-- final constraint. Only values in the paernt root may appear in the
-- extension (see X.680 section G.4.2.3).
{-
applyExtWithRt :: IntConstraint -> IntConstraint -> IntConstraint
applyExtWithRt a b = serialC a b
-}

lApplyExtWithRt :: (Eq a, L.Lattice a, Show a, MonadError [Char] m) =>
                   m a -> m a -> m a
lApplyExtWithRt a b = lSerialC a b

-- need to define encInt
{-
encInt :: Maybe (Int,Int) -> Maybe (Int,Int) -> Bool -> Int -> BitStream
encInt r e b v = []
-}
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

lApplyIntCons :: (MonadError String m, L.Lattice (m L.IntegerConstraint)) =>
                 m L.IntegerConstraint -> [ESS Integer] -> m L.IntegerConstraint
lApplyIntCons x [] = x
lApplyIntCons x (c:cs) = lApplyIntCons (lEvalC c x) cs

{-
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
-}

lEvalC :: (L.Lattice (m L.IntegerConstraint), MonadError String m) =>
          ESS Integer -> m L.IntegerConstraint -> m L.IntegerConstraint
lEvalC (RE c) x       = lSerialC x (lCalcC c)
lEvalC (EXT c) x      = lSerialC x (lCalcC c)
lEvalC (EXTWITH c d) x = lSerialC x (lCalcC c)

-- See X.680 section G.4.2.3 for details on the serial application
-- of constraints. The second input is the new constraint whose
-- values must be bounded by the values in the first input. Thus
-- minBound in the second input matches the lower bound in the first
-- input and similarly for maxBound. Note that serialC takes two
-- Maybe type inputs since the illegal first input has already been
-- dealt with by applyIntCons. The second input cannot be illegal
-- since this is simply the (possible) set combination of atomic
-- constraints and involves no serial application of constraints.

lSerialC :: (MonadError [Char] m, Show a, L.Lattice a, Eq a) =>
            m a -> m a -> m a
lSerialC mx my =
   do a <- mx
      b <- my
      let foobar
             | b == L.bottom =
                  return L.bottom
             | a `L.meet` b == b =
                  return (a `L.meet` b)
             | otherwise =
                  throwError ("Constraint and parent type mismatch: " ++ show a ++ " does not match " ++ show b) -- Somehow we should prettyConstraint here
      foobar
{-
calcC :: Constr Int -> IntConstraint
calcC (UNION u) = calcU u
calcC (ALL e)   = exceptC (Left (Just (minBound,maxBound))) (calcEx e)
-}
lCalcC :: (MonadError String m, L.Lattice (m L.IntegerConstraint)) =>
          Constr Integer -> m L.IntegerConstraint
lCalcC (UNION u) = lCalcU u

-- Need to define unionC which returns the union of two
-- constraints
{-
calcU :: Union Int -> IntConstraint
calcU (IC i )  = calcI i
calcU (UC u i) = let x = calcU u
                     y = calcI i
                 in unionC x y
-}
lCalcU :: (L.Lattice (m L.IntegerConstraint), MonadError String m) =>
          Union Integer -> m L.IntegerConstraint
lCalcU (IC i) = lCalcI i
lCalcU(UC u i) = (lCalcU u) `L.ljoin` (lCalcI i)

{-
calcI :: IntCon Int -> IntConstraint
calcI (INTER i e) = let x = calcI i
                        y = calcA e
                    in interC x y
calcI (ATOM a)    = calcA a
-}
lCalcI :: (MonadError String m, L.Lattice (m L.IntegerConstraint)) =>
          IntCon Integer -> m L.IntegerConstraint
lCalcI (INTER i e) = (lCalcI i) `L.meet` (lCalcA e)
lCalcI (ATOM a)    = lCalcA a

lCalcA :: (L.Lattice (m L.IntegerConstraint), MonadError String m) =>
          IE Integer -> m L.IntegerConstraint
lCalcA (E e) = lCalcE e

-- Note that the resulting constraint is always a contiguous set.

-- Need processCT to process the constraint implications of type
-- inclusion.
-- NOTE: Need to deal with illegal constraints resulting from
-- processCT
{-
calcE :: Elem Int -> IntConstraint
calcE (S (SV i))    = Left (Just (i,i))
calcE (C (Inc t))   = processCT t []
calcE (V (R (l,u))) = Left (Just (l,u))
-}

lCalcE :: (MonadError String m, L.Lattice (m L.IntegerConstraint)) =>
          Elem Integer -> m L.IntegerConstraint
lCalcE (S (SV i)) = return (L.IntegerConstraint (L.V i) (L.V i))
lCalcE (C (Inc t)) = lProcessCT t []
lCalcE (V (R (l,u))) = return (L.IntegerConstraint (L.V l) (L.V u))
{-
calcEx :: Excl Int -> IntConstraint
calcEx (EXCEPT e) = calcE e
-}
-- Need to define reference case which requires derefencing.
-- This function is similar to the encode function in that it
-- needs to produce the effective constraint for the included type.
{-
processCT :: ASNType Int -> [ESS Int] -> IntConstraint
processCT (BT INTEGER) cl = applyIntCons (Left (Just (minBound,maxBound))) cl
processCT (RT r) cl       = error "Need to do"
processCT (ConsT t c) cl  = processCT t (c:cl)
-}
lProcessCT :: (L.Lattice (m L.IntegerConstraint), MonadError String m) => ASNType Integer -> [ESS Integer] -> m L.IntegerConstraint
lProcessCT (BT INTEGER) cl = lApplyIntCons L.top cl
lProcessCT (ConsT t c) cl    = lProcessCT t (c:cl)


\end{code}

27 ENCODING THE VISIBLESTRING (KNOWN-MULTIPLIER CHARACTER STRING) TYPE

If the type is extensible then a single bit shall be added to the
encoding. This is set to 0 if the value is withing the range of
the extension root and to 1 otherwise. If the value is outside the
range then the encoding shall be as if there was no effective size
constraint and shall have an effective permitted alphabet
constraint that consists of the set of characters of the
unconstrained type.

The first case of encodeVisString is for an unconstrained value.

\begin{code}
{-
encodeVisString :: [ESS VisibleString] -> VisibleString -> Either BitStream String
encodeVisString [] vs = Left (encodeVis vs)
encodeVisString cs vs
    = let ec = serialResEffCons (Left ((vsNoConstraint,vsNoConstraint),False)) cs
      in
        encVS ec vs
-}

lEncodeVisString :: (L.Lattice (m (L.ExtResStringConstraint VisibleString)),
                     L.Lattice (m (L.ResStringConstraint VisibleString)),
                     RST m VisibleString,
                     MonadError String m) =>
                     [ESS VisibleString] -> VisibleString -> m BP.BitPut
lEncodeVisString [] vs = return (bitPutify (encodeVis vs))
lEncodeVisString cs vs
    = lEncVS (lSerialResEffCons L.top cs) vs


-- The first case of encVS deals with non-per visible constraint.
-- If the constraint is non-per visible then we treat the value as
-- unconstrained.
-- NEED TO DEAL WITH CASE WHEN ROOT AND EXTENSION ARE DIFFERENT
-- CONSTRAINTS

stringMatch :: String -> String -> Bool
stringMatch [] s = True
stringMatch (f:r) s = elem f s && stringMatch r s

{- The invisible case in encVS should be dealt with when generated
in a sub-function -}

lEncVS :: (MonadError [Char] m,
           L.Lattice (m (L.ExtResStringConstraint VisibleString)))
                      => m (L.ExtResStringConstraint VisibleString) -> VisibleString
                          -> m BP.BitPut
lEncVS m v
    = do
        vsc <- m
        if L.extensible vsc
            then lEncExtVS m v
            else lEncNonExtVS m v


{-
A value is out of range if it is not within the constraint. This
includes the cases where either the size or PA constraint is
bottom which by default cannot be satisfied.
No constraint is represented by the lattice attribute top which is
the default value when generating an effective constraint.
-}
lEncNonExtVS :: (MonadError [Char] m,
                 L.Lattice (m (L.ExtResStringConstraint VisibleString)))
                      => m (L.ExtResStringConstraint VisibleString) -> VisibleString
                          -> m BP.BitPut
lEncNonExtVS m vs@(VisibleString v)
    = do
        vsc <- m
        let rc = L.getRC vsc
            sc = L.getSC rc
            pac = L.getPAC rc
            emptyConstraint = rc == L.bottom
            noSC  = sc == L.top
            noPAC = pac == L.top
            inSizeRange x = let l = genericLength v
                            in (L.V l) >= (L.lower x) &&  (L.V l) <= (L.upper x)
            inPA (VisibleString x)  = stringMatch v x
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | not noSC && not noPAC && inPA pac && inSizeRange sc
                    = return (bitPutify (lEncodeVisSzF sc pac vs))
                | noSC && not noPAC && inPA pac
                    = return (bitPutify (lEncodeVisF pac vs))
                | noPAC && not noSC && inSizeRange sc
                    = return (bitPutify (lEncodeVisSz sc vs))
                | otherwise
                    = throwError "Value out of range"
        foobar


lEncExtVS :: (MonadError [Char] m,
                 L.Lattice (m (L.ExtResStringConstraint VisibleString)))
                      => m (L.ExtResStringConstraint VisibleString) -> VisibleString
                          -> m BP.BitPut
lEncExtVS m vs@(VisibleString v)
    = do
        vsc <- m
        let rc = L.getRC vsc
            ec = L.getEC vsc
            rsc = L.getSC rc
            rpac = L.getPAC rc
            esc = L.getSC ec
            epac = L.getPAC ec
            expac = let VisibleString r = L.getPAC rc
                        VisibleString e = L.getPAC ec
                    in VisibleString (r++e)
            emptyConstraint = vsc == L.bottom
            noRC  = rc == L.top
            noEC  = ec == L.top
            noRSC  = rsc == L.top
            noRPAC = rpac == L.top
            noESC  = esc == L.top
            noEPAC = epac == L.top
            inSizeRange x = let l = genericLength v
                            in (L.V l) >= (L.lower x) &&  (L.V l) <= (L.upper x)
            inPA (VisibleString x)  = stringMatch v x
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | otherwise = foobarREC
            foobarREC
                | noEC = foobarRC
                | noRC = foobarEC
                | otherwise = foobarBoth
            foobarRC
                | noRSC && inPA rpac
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisF rpac vs)
                | noRPAC && inSizeRange rsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSz rsc vs)
                | inPA rpac && inSizeRange rsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSzF rsc rpac vs)
                | otherwise
                    = throwError "Value out of range"
            foobarEC
                | noESC && inPA epac
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (lEncodeVisF L.top vs)
                | noEPAC && inSizeRange esc
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (encodeVis vs)
                | inPA epac && inSizeRange esc
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (lEncodeVisF L.top vs)
                | otherwise
                    = throwError "Value out of range"
            foobarBoth
                | not noRPAC && inPA rpac && not noRSC && inSizeRange rsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSzF rsc rpac vs)
                | noRPAC && noEPAC && not noRSC && inSizeRange rsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSz rsc vs)
                | noRSC && noESC && not noRPAC && inPA rpac
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisF rpac vs)
                | noRPAC && noEPAC && not noESC && inSizeRange esc
                     = return $ do BP.putNBits 1 (1::Int)
                                   bitPutify (encodeVis vs)
                | (not noRSC && inSizeRange rsc && noRPAC && not noEPAC && inPA epac) ||
                  (not noRSC && inSizeRange rsc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (not noESC && inSizeRange esc && not noRPAC && inPA rpac) ||
                  (not noESC && inSizeRange esc && noRPAC && not noEPAC && inPA epac) ||
                  (not noESC && inSizeRange esc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (noRSC && noESC && ((noRPAC && not noEPAC && inPA epac) ||
                  (not noRPAC && not noEPAC && not (inPA epac) && inPA expac)))
                     =  return $ do BP.putNBits 1 (1::Int)
                                    bitPutify (lEncodeVisF L.top vs)
                | otherwise
                     = throwError "Value out of range"
        foobar

lEncodeVisSz :: L.IntegerConstraint -> VisibleString -> BitStream
lEncodeVisSz (L.IntegerConstraint l u) v = manageExtremes encS (encodeVis . VisibleString) l u
                                                (L.getString v)



encodeVis :: VisibleString -> BitStream
encodeVis (VisibleString s)
    = encodeWithLength encS s



encC c  = encodeNNBIntBits ((fromIntegral.ord) c, 94)
encS s  = (concat . map encC) s

\end{code}

 27.5.4 Encoding of a VISIBLESTRING with a permitted alphabet
 constraint.

\begin{code}

lEncodeVisSzF :: L.IntegerConstraint -> VisibleString -> VisibleString -> BitStream
lEncodeVisSzF (L.IntegerConstraint l u) vsc@(VisibleString s) (VisibleString xs)
        =  manageExtremes (encSF s) (lEncodeVisF vsc . VisibleString) l u xs

{-
encodeVisF :: String -> VisibleString -> BitStream
encodeVisF str (VisibleString s)
    = encodeWithLength (encSF str) s
-}

lEncodeVisF :: VisibleString -> VisibleString -> BitStream
lEncodeVisF (VisibleString s) (VisibleString v) = encodeWithLength (encSF s) v


encSF p str
    = let sp  = sort p
          lp  = genericLength p
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

manageExtremes :: ([a] -> BitStream) -> ([a] -> BitStream) -> L.InfInteger
                        -> L.InfInteger -> [a] -> BitStream
manageExtremes fn1 fn2 l@(L.V v) u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
               then fn1 x
               else if u >= 65536
                   then fn2 x
                   else let L.V r = range
                        in
                        encodeNNBIntBits ((genericLength x-v),r-1) ++ fn1 x

\end{code}

Clause 38.8 in X680 (Canonical ordering of VisibleString characters)

\begin{code}


canEnc b sp [] = []
canEnc b sp (f:r)
        = let v = (genericLength . findV f) sp
           in encodeNNBIntBits (v,b) : canEnc b sp r

findV m []  = []
findV m (a:rs)
          = if m == a
                then []
                else a : findV m rs



\end{code}


\begin{code}

type ElementSetSpecs a = ESS a

decode :: (MonadError [Char] (t BG.BitGet), MonadTrans t) => ASNType a -> [ElementSetSpecs a] -> t BG.BitGet a
decode (BT t) cl = fromPer t cl
decode (ConsT t c) cl = decode t (c:cl)

decode2 (BT t) cl = fromPer2 t cl
decode2 (ConsT t c) cl = decode2 t (c:cl)

fromPer :: (MonadError [Char] (t BG.BitGet), MonadTrans t) => ASNBuiltin a -> [ElementSetSpecs a] -> t BG.BitGet a
fromPer t@INTEGER cl  = decodeInt cl

fromPer2 :: (MonadError [Char] (t BG.BitGet), MonadTrans t, L.Lattice (m L.IntegerConstraint), MonadError String m) =>
   ASNBuiltin a -> [ElementSetSpecs a] -> m (t BG.BitGet a)
fromPer2 t@INTEGER cl = decodeInt2 cl

decodeInt [] = decodeUInt >>= \x -> return (fromIntegral x)

decodeInt2 [] = error "you haven't done unconstrained decoding!"
decodeInt2 cs =
   lEitherTest2 parentRoot lc
   where
      lc         = last cs
      ic         = init cs
      parentRoot = lApplyIntCons L.top ic

lEitherTest2 pr lc =
   lDecConsInt2 effRoot effExt
   where
      (effExt,b) = lApplyExt pr lc
      effRoot    = lEvalC lc pr

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

-- lDecConsInt2 :: (MonadError [Char] m) => m L.IntegerConstraint -> m L.IntegerConstraint -> m (BG.BitGet Integer)
lDecConsInt2 mrc mec =
   do rc <- mrc
      ec <- mec
      let extensionConstraint    = ec /= L.bottom
          extensionRange         = (L.upper ec) - (L.lower ec) + 1
          rootConstraint         = rc /= L.bottom
          rootLower              = let L.V x = L.lower rc in x
          rootRange              = fromIntegral $ let (L.V x) = (L.upper rc) - (L.lower rc) + (L.V 1) in x -- fromIntegral means there's an Int bug lurking here
          numOfRootBits          = genericLength (encodeNNBIntBits (rootRange - 1, rootRange - 1))
          emptyConstraint        = (not rootConstraint) && (not extensionConstraint)
          inRange v x            = (L.V v) >= (L.lower x) &&  (L.V v) <= (L.upper x)
          unconstrained x        = (L.lower x) == minBound
          semiconstrained x      = (L.upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | rootConstraint &&
               extensionConstraint
                  = error "Root constraint and extension constraint and in range"
             | rootConstraint
                  = return $ if rootRange <= 1
                                then
                                   return rootLower
                                else
                                   do isExtension <- lift $ BG.getBit
                                      if isExtension
                                         then
                                            throwError "Extension for constraint not supported"
                                         else
                                            do j <- lift $ BG.getLeftByteString numOfRootBits
                                               let v = rootLower + (fromNonNeg numOfRootBits j)
                                               if v `inRange` rc
                                                  then
                                                     return v
                                                  else
                                                     throwError "Value not in root constraint"

             | extensionConstraint
               -- inRange ec
                  = error "Extension constraint and in range"
             | otherwise
                  = throwError "Value out of range"
      foobar

\end{code}

\bibliographystyle{plainnat}

\bibliography{3gpp,ASN1}

\end{document}
