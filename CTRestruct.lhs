\documentclass{article}
%include polycode.fmt

\usepackage{listings}

\lstdefinelanguage{ASN1} {
  keywords={CHOICE, SEQUENCE, BEGIN, END, IMPLICIT, EXPLICIT, INTEGER, DEFINITIONS},
  sensitive=false,
  morecomment=[s]{(--}{--)}
  }

\lstnewenvironment{asn1}[1][]
  {\lstset{language=ASN1,captionpos=b,frame=single,basicstyle=\scriptsize,float,#1}}
  {}

\newcommand{\bottom}{\perp}

\begin{document}

\title{A Formal and Executable Specification of the ASN.1 Packed Encoding Rules}

\author{D. J. Russell \and D. J. Steinitz}

\maketitle

\section{Introduction}

ASN.1~\cite{PER} --- Abstract Syntax Notation --- is a large and complex specification for the abstract defininition of data
for exchange between heterogeneous systems
together with several concrete encodings~\cite{PER}. It is widely used, for example, to describe digital certificates, in
third generation mobile telephony~\cite{3gpp.25.413} and in aviation~\cite{ACARS,ACARSInterop,FANS,ATN}.

An example ASN.1 specification is shown in Figure~\ref{lst:ExampleASN1}.

\begin{asn1}[caption={Example ASN.1},label=lst:ExampleASN1]
FooBar {1 2 3 4 5 6} DEFINITIONS ::=
  BEGIN
    Type9 ::=
      CHOICE {
        element1 [0] IMPLICIT INTEGER,
        element2 [1] EXPLICIT CHOICE {
          subElement1 [3] IMPLICIT INTEGER,
          subElement2 [4] IMPLICIT INTEGER,
          subElement3 [5] IMPLICIT INTEGER
        },
        element4 [2] IMPLICIT INTEGER
      }
    Type12 ::=
      CHOICE {
        c1 [0] IMPLICIT SEQUENCE {
          one INTEGER,
          two INTEGER
        },
        c2 [1] IMPLICIT SEQUENCE {
          three INTEGER,
          four INTEGER
        }
      }
  END
\end{asn1}

\section{Housekeeping}

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
import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String,
                ComponentType(Default), NamedType, OctetString)
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

data Sz a = SizeConstraint a => SC (ESS L.InfInteger)

data PA a = PermittedAlphabet a => FR (ESS a)

--IS to be completed for multiple type constraints
data IS a = InnerType a => WC (ESS a) | WCS

-- Type constraint (constraining an open type) to be done (47.6)
-- Pattern constraint to be done.
\end{code}

X.680 16.1

Type ::= BuiltinType | ReferencedType | ConstrainedType

\begin{code}
data ASNType a where
    BT    :: ASNBuiltin a -> ASNType a
    RT    :: ReferencedType -> ASNType a
    ConsT :: ASNType a -> ESS a -> ASNType a

data ASNBuiltin a where
   EXTADDGROUP     :: Sequence a -> ASNBuiltin a
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin L.InfInteger
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
--newtype VisibleString = VisibleString {visibleString :: String}
--    deriving (Eq, Show)

type BitStream = [Int]
type Octet = Word8
type OctetStream = [Octet]

type TagInfo    = (TagType, TagValue, TagPlicity)
type TypeRef    = String
type Name       = String

\end{code}

Type Classes which make explicit the (not necessarily PER-visible) subtypes associated with the ASN.1 types.

See X.680 (07/2002) Section 47.1 Table 9

RST is a type class for the restricted character string types.

\begin{code}

class SingleValue a

instance SingleValue BitString
instance SingleValue IA5String
instance SingleValue PrintableString
instance SingleValue L.InfInteger
instance SingleValue VisibleString

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype IA5String
instance ContainedSubtype PrintableString
instance ContainedSubtype NumericString
instance ContainedSubtype L.InfInteger

class ValueRange a

instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange L.InfInteger


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
data Sequence a where
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

data ComponentType a where
   CTMandatory :: NamedType a -> ComponentType a
   CTExtMand   :: NamedType a -> ComponentType (Maybe a)
   CTOptional  :: NamedType a -> ComponentType (Maybe a)
   CTDefault   :: NamedType a -> a -> ComponentType (Maybe a)
   CTCompOf    :: ASNType a   -> ComponentType a

data NamedType a where
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

data Choice a where
    NoChoice     :: Choice Nil
    ChoiceExt    :: Choice l -> Choice l
    ChoiceEAG    :: Choice l -> Choice l
    ChoiceOption :: NamedType a -> Choice l -> Choice (a:*:l)

data HL a l where
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

data EnumerationItem a where
    Identifier :: Name -> EnumerationItem Name
    NamedNumber :: Name -> Int -> EnumerationItem Name

data Enumerate a where
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
lEncode (BT t) v cl      = lToPer t v cl
lEncode (RT _) _ _       = error "RT"
lEncode (ConsT t c) v cl = lEncode t v (c:cl)

\end{code}

need to deal with per-visible constraint list here.
generate effective root and effective extension here.

\begin{code}

lToPer :: (L.Lattice (m L.IntegerConstraint),
           L.Lattice (m L.ValidIntegerConstraint),
           L.Lattice (m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)),
           L.Lattice (m (L.ResStringConstraint L.IntegerConstraint VisibleString)),
           L.Lattice (m (L.ExtResStringConstraint L.ValidIntegerConstraint VisibleString)),
           L.Lattice (m (L.ResStringConstraint L.ValidIntegerConstraint VisibleString)),
           L.BooleanAlgebra (m L.ValidIntegerConstraint),
           MonadError [Char] m)
            => ASNBuiltin a -> a -> [ESS a] -> m BP.BitPut
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
-- ResStringConstraint is a parameterised type (to allow for the different restricted string types)
-- encompassing the (size,permittedAlphabet) constraint pair.


serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
--- effective constraint (if it exists).

{- NOTE WE WANT THE TYPE TO BE MORE GENERAL e.g. replaced VisibleString with RS a => a -}

serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

\begin{code}

lSerialResEffCons :: (MonadError [Char] m,
                      Eq t1,
                      Eq t,
                      Show t,
                      L.Lattice t1,
                      L.Lattice t,
                      L.Lattice (m t),
                      L.Lattice (m (L.ExtResStringConstraint t t1)),
                      L.IC t,
                      L.RS t1) =>
                      m (L.ExtResStringConstraint t t1) -> [ESS t1]
                      -> m (L.ExtResStringConstraint t t1)
lSerialResEffCons m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = lSerialApplyLast esrc c
                        foobar1 (f:r) = lSerialResEffCons (lSerialApply esrc f) r
                    foobar1 ls
        foobar


lSerialApply :: (MonadError [Char] m,
                 Eq a,
                 Eq i,
                 Show i,
                 L.Lattice a,
                 L.Lattice i,
                 L.Lattice (m i),
                 L.Lattice (m (L.ExtResStringConstraint i a)),
                 L.IC i,
                 L.RS a) =>
                 L.ExtResStringConstraint i a -> ESS a -> m (L.ExtResStringConstraint i a)
lSerialApply ersc c = lEitherApply ersc (lResEffCons c 0)

\end{code}

\begin{code}

lEitherApply :: (MonadError [Char] m,
                 Eq i,
                 Eq a,
                 Show i,
                 L.Lattice i,
                 L.Lattice a,
                 L.IC i,
                 L.RS a) =>
                 L.ExtResStringConstraint i a -> m (L.ExtResStringConstraint i a)
                 -> m (L.ExtResStringConstraint i a)
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
        foobar

--lValidResCon :: (L.Lattice a, L.RS a, Eq a) => L.ResStringConstraint a -> L.ResStringConstraint a -> Bool
lValidResCon (L.ResStringConstraint s1 p1) (L.ResStringConstraint s2 p2)
    = L.within s1 s2 && lValidPA p1 p2



lValidPA :: (L.Lattice a, L.RS a, Eq a) => a -> a -> Bool
lValidPA x y
    = if x == L.top || y == L.top
        then True
        else and (map (flip elem (L.getString x)) (L.getString y))


lUpdateResCon :: (L.IC t, L.Lattice t1, L.RS t1, Eq t1) =>
                 L.ResStringConstraint t t1
                 -> L.ResStringConstraint t t1
                 -> L.ResStringConstraint t t1
lUpdateResCon (L.ResStringConstraint s1 p1) (L.ResStringConstraint s2 p2)
     = L.ResStringConstraint (L.serialCombine s1 s2) (lUpdatePA p1 p2)



lUpdatePA :: (L.Lattice a, L.RS a, Eq a) => a -> a -> a
lUpdatePA x y
    = if x == L.bottom || y == L.bottom
        then L.bottom
        else y

lSerialApplyLast :: (MonadError [Char] m,
                     Eq t1,
                     Eq t,
                     Show t,
                     L.Lattice t1,
                     L.Lattice t,
                     L.Lattice (m t),
                     L.Lattice (m (L.ExtResStringConstraint t t1)),
                     L.IC t,
                     L.RS t1) =>
                     L.ExtResStringConstraint t t1 -> ESS t1 -> m (L.ExtResStringConstraint t t1)
lSerialApplyLast x c = lLastApply x (lResEffCons c 0)


lLastApply :: (Eq t1,
               L.RS t1,
               L.Lattice t1,
               L.IC t,
               L.Lattice t,
               Eq t,
               Show t,
               MonadError [Char] m) =>
               L.ExtResStringConstraint t t1 -> m (L.ExtResStringConstraint t t1)
               -> m (L.ExtResStringConstraint t t1)
lLastApply (L.ExtResStringConstraint r1 _ _) m
    = do
         let foobar
                 = do
                    x@(L.ExtResStringConstraint r2 e2 _) <- m
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

lResEffCons :: (MonadError [Char] m,
                L.RS t,
                L.IC i,
                L.Lattice i,
                L.Lattice t,
                L.Lattice (m i),
                L.Lattice (m (L.ExtResStringConstraint i t)),
                Eq i,
                Show i,
                Eq t) =>
                ESS t -> Int ->  m (L.ExtResStringConstraint i t)
lResEffCons (RE c) n        = lResCon c False n
lResEffCons (EXT c) n       = lResCon c True n
lResEffCons (EXTWITH c e) n = lExtendResC (lResCon c False n) (lResCon e False n)

\end{code}

resCon processes constraints. Its second input indicates if the
type is extensible.

\begin{code}

lResCon :: (MonadError [Char] m,
            Eq a,
            Eq i,
            Show i,
            L.Lattice a,
            L.Lattice i,
            L.Lattice (m i),
            L.IC i,
            L.RS a,
            L.Lattice (m (L.ExtResStringConstraint i a))) =>
            Constr a -> Bool -> Int ->  m (L.ExtResStringConstraint i a)
lResCon (UNION u) b n        = lResConU u b n
lResCon (ALL (EXCEPT e)) b n = lResExceptAll L.top (conE e b n)

\end{code}

extendresC implements the extension operator (...) on visiblestring
constraints.
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)

\begin{code}

lExtendResC :: (MonadError [Char] m,
                Eq t,
                Eq t1,
                L.Lattice t,
                L.Lattice t1,
                L.IC t,
                L.RS t1) =>
                m (L.ExtResStringConstraint t t1)
                -> m (L.ExtResStringConstraint t t1)
                -> m (L.ExtResStringConstraint t t1)
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

lResExceptAll :: (MonadError [Char] m,
                  L.IC i,
                  Eq i,
                  Eq a,
                  L.RS a,
                  L.Lattice i,
                  L.Lattice a) =>
                  L.ResStringConstraint i a -> m (L.ExtResStringConstraint i a)
                  -> m (L.ExtResStringConstraint i a)
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


lResConU :: (MonadError [Char] m,
             L.RS t,
             L.IC i,
             L.Lattice i,
             L.Lattice t,
             L.Lattice (m i),
             L.Lattice (m (L.ExtResStringConstraint i t)),
             Eq i,
             Show i,
             Eq t) =>
             Union t -> Bool -> Int -> m (L.ExtResStringConstraint i t)
lResConU (IC i) b  n  = lResConI i b n
lResConU (UC u i) b n = lUnionResC (lResConI i b n) (lResConU u False n)

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

lUnionResC :: (MonadError [Char] m,
               L.IC i,
               Eq i,
               Eq a,
               L.RS a,
               L.Lattice i,
               L.Lattice a) =>
               m (L.ExtResStringConstraint i a)
               -> m (L.ExtResStringConstraint i a)
               -> m (L.ExtResStringConstraint i a)
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

lResConI :: (MonadError [Char] m,
             Eq t,
             Eq i,
             Show i,
             L.Lattice t,
             L.Lattice i,
             L.Lattice (m i),
             L.Lattice (m (L.ExtResStringConstraint i t)),
             L.IC i,
             L.RS t) =>
             IntCon t -> Bool -> Int -> m (L.ExtResStringConstraint i t)
lResConI (INTER i e) b n = lInterResC (lResConA e b n) (lResConI i False n)
lResConI (ATOM e) b n    = lResConA e b n

\end{code}

interResC implements the intersection of visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lInterResC :: (MonadError e m,
               Eq i,
               Eq a,
               L.Lattice i,
               L.Lattice a,
               L.IC i,
               L.RS a) =>
               m (L.ExtResStringConstraint i a)
               -> m (L.ExtResStringConstraint i a)
               -> m (L.ExtResStringConstraint i a)
lInterResC m n
    = do
         let foobar1 x
                 = do catchError (do c2 <- n
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
                = catchError (do c1 <- m
                                 foobar1 c1)
                             (\err -> n)
         foobar

\end{code}

resConA deals with atomic (including except) constraints

\begin{code}

lResConA :: (MonadError [Char] m,
             Eq t,
             Eq i,
             Show i,
             L.Lattice t,
             L.Lattice i,
             L.Lattice (m i),
             L.Lattice (m (L.ExtResStringConstraint i t)),
             L.IC i,
             L.RS t) =>
             IE t -> Bool -> Int -> m (L.ExtResStringConstraint i t)
lResConA (E e) b n = conE e b n
lResConA (Exc e (EXCEPT ex)) b n
                = lExceptResC (conE e b n) (conE ex False n)

\end{code}

resExcept implements the set difference operator applied to
visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lExceptResC :: (MonadError [Char] m,
                L.IC i,
                Eq i,
                Eq a,
                L.RS a,
                L.Lattice i,
                L.Lattice a) =>
                m (L.ExtResStringConstraint i a)
                -> m (L.ExtResStringConstraint i a)
                -> m (L.ExtResStringConstraint i a)
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

conE e b n
    | n == 0 = lResConE e b
    | otherwise = lPaConE e b

lResConE :: (MonadError [Char] m,
             Eq a,
             Eq i,
             Show i,
             L.Lattice a,
             L.Lattice i,
             L.Lattice (m i),
             L.Lattice (m (L.ExtResStringConstraint i a)),
             L.IC i,
             L.RS a) =>
             Elem a -> Bool -> m (L.ExtResStringConstraint i a)
lResConE (SZ (SC v)) b            = lEffResSize v b
lResConE (P (FR (EXT _))) b       = throwError "Invisible!"
lResConE (P (FR (EXTWITH _ _))) b = throwError "Invisible!"
lResConE (P (FR (RE p)))  b       = lResEffCons (RE p) 1
lResConE (C (Inc c)) b            = lProcessCST c []
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

lPaConE :: (MonadError [Char] m,
            L.Lattice a,
            L.Lattice a1,
            L.RS a,
            Eq a,
            Eq a1,
            Show a1,
            L.Lattice (m a1),
            L.Lattice (m (L.ExtResStringConstraint a1 a)),
            L.IC a1) =>
            Elem a -> Bool -> m (L.ExtResStringConstraint a1 a)
lPaConE (V (R (l,u))) b
    = let ls = L.getString l
          us = L.getString u
          rs = [head ls..head us]
        in
            return (L.ExtResStringConstraint (L.ResStringConstraint L.top (L.putString rs))
                        (L.ResStringConstraint L.top L.top) b)
lPaConE (C (Inc c)) b = lProcessCST c []
lPaConE (S (SV v)) b
   = return (L.ExtResStringConstraint (L.ResStringConstraint L.top v)
                                      (L.ResStringConstraint L.top L.top) b)


lEffResSize :: (MonadError [Char] t,
                L.IC t1,
                L.Lattice (t t1),
                L.Lattice a,
                L.Lattice t1,
                L.RS a,
                Eq a,
                Eq t1,
                Show t1) =>
                ESS L.InfInteger -> Bool -> t (L.ExtResStringConstraint t1 a)
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

lProcessCST :: (MonadError [Char] m,
                Eq a,
                Eq i,
                Show i,
                L.Lattice a,
                L.Lattice i,
                L.Lattice (m i),
                L.Lattice (m (L.ExtResStringConstraint i a)),
                L.IC i,
                L.RS a) => ASNType a -> [ESS a] -> m (L.ExtResStringConstraint i a)
lProcessCST (BT _) cl = lRootStringCons L.top cl
lProcessCST (ConsT t c) cl = lProcessCST t (c:cl)


lRootStringCons t cs
    = let m = lSerialResEffCons t cs
      in do
            (L.ExtResStringConstraint r e _) <- m
            return (L.ExtResStringConstraint r L.top False)

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

myEncodeUInt (L.V x)
    = (bitPutify . encodeUInt . fromIntegral) x

lEncodeInt :: (L.Lattice (m L.IntegerConstraint),
               L.BooleanAlgebra (m L.ValidIntegerConstraint), MonadError [Char] m)
                 => [ESS L.InfInteger] -> L.InfInteger -> m BP.BitPut
lEncodeInt [] v = return (myEncodeUInt v)
lEncodeInt cs v =
   lEitherTest parentRoot validPR lc v
   where
      lc         = last cs
      ic         = init cs
      parentRoot :: (MonadError [Char] m, L.Lattice (m L.IntegerConstraint))
                    => m L.IntegerConstraint
      parentRoot = lRootIntCons L.top ic
      validPR :: (MonadError [Char] m, L.BooleanAlgebra (m L.ValidIntegerConstraint))
                    => m L.ValidIntegerConstraint
      validPR    = lRootIntCons L.top ic



lEitherTest :: (MonadError String m, L.Lattice (m L.IntegerConstraint),
                L.BooleanAlgebra (m L.ValidIntegerConstraint)) =>
               m L.IntegerConstraint -> m L.ValidIntegerConstraint
               -> ESS L.InfInteger -> L.InfInteger -> m BP.BitPut
lEitherTest pr vpr lc v =
   lEncConsInt realRoot realExt effRoot effExt b v
   where
      (effExt,b)  = lApplyExt pr lc
      effRoot     = lEvalC lc pr
      (realExt,b2) = lApplyExt vpr lc
      realRoot    = lEvalC lc vpr

\end{code}

See Section 12 of X.691 (Encoding the Integer type).
\begin{code}

lEncConsInt :: (MonadError [Char] m, Eq t, L.Lattice t) =>
               m L.ValidIntegerConstraint
               -> m L.ValidIntegerConstraint
               -> m L.IntegerConstraint
               -> m t
               -> Bool
               -> L.InfInteger
               -> m BP.BitPut
lEncConsInt rootCon extCon effRootCon effExtCon extensible v
    = if (not extensible)
        then lEncNonExtConsInt rootCon effRootCon v
        else lEncExtConsInt rootCon extCon effRootCon effExtCon v


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

lEncExtConsInt :: (MonadError [Char] m, Eq t, L.Lattice t) =>
                  m L.ValidIntegerConstraint
                  -> m L.ValidIntegerConstraint
                  -> m L.IntegerConstraint
                  -> m t
                  -> L.InfInteger
                  -> m BP.BitPut
lEncExtConsInt realRC realEC effRC effEC n@(L.V v) =
   do
      L.Valid rrc <- realRC
      L.Valid rec <- realEC
      erc <- effRC
      eec <- effEC
      let isNonEmptyEC           = eec /= L.bottom
          isNonEmptyRC           = erc /= L.bottom
          emptyConstraint        = (not isNonEmptyRC) && (not isNonEmptyEC)
          inRange []             = False
          inRange (x:rs)         = n >= (L.lower x) && n <= (L.upper x) || inRange rs
          unconstrained x        = (L.lower x) == minBound
          semiconstrained x      = (L.upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          L.V rootLower              = L.lower erc
          L.V rootUpper              = L.upper erc
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rrc
                  = return $ do BP.putNBits 1 (0::Int)
                                case constraintType erc of
                                   UnConstrained ->
                                      bitPutify (encodeUInt (fromIntegral v))
                                   SemiConstrained ->
                                      bitPutify (encodeSCInt (fromIntegral v) rootLower)
                                   Constrained ->
                                      bitPutify (encodeNNBIntBits (fromIntegral (v - rootLower), fromIntegral (rootUpper - rootLower)))
             | isNonEmptyEC && inRange rec
                  = return $ do BP.putNBits 1 (1::Int)
                                bitPutify (encodeUInt (fromIntegral v))
             | otherwise
                  = throwError "Value out of range"
      foobar

lEncNonExtConsInt :: (MonadError [Char] m) =>
                     m L.ValidIntegerConstraint
                     -> m L.IntegerConstraint
                     -> L.InfInteger
                     -> m BP.BitPut
lEncNonExtConsInt realRC effRC n@(L.V v) =
   do L.Valid rrc <- realRC
      erc <- effRC
      let isNonEmptyRC           = erc /= L.bottom
          emptyConstraint        = not isNonEmptyRC
          inRange []             = False
          inRange (x:rs)         = n >= (L.lower x) && n <= (L.upper x) || inRange rs
          unconstrained x        = (L.lower x) == minBound
          semiconstrained x      = (L.upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          L.V rootLower          = L.lower erc
          L.V rootUpper          = L.upper erc
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rrc
                  = return $ do
                       case constraintType erc of
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

lApplyExt :: (L.Lattice (m a), MonadError [Char] m, L.IC a, Eq a, L.Lattice a, Show a) =>
             m a -> ESS L.InfInteger -> (m a, Bool)
lApplyExt rp (RE _)  = (L.bottom, False)
lApplyExt rp (EXT _) = (L.bottom, False)
lApplyExt rp (EXTWITH _ c) = (lApplyExtWithRt rp (lCalcEC c), True)

-- Need to define calcEC (follow rules outlined in X.680 G.4.3.8)
-- and appExtWithRt
-- For Integer constraints, set operators are only applied to
-- non-extensible constraints (see 47.2 and 47.4 for definitions of
-- SingleValue and ValueRange constraints) and thus calcEC is simply
-- calcC. Thus G.4.3.8 can be ignored.

lCalcEC :: (MonadError [Char] m, L.IC a, L.Lattice (m a),
            L.Lattice a, Show a, Eq a) =>
           Constr L.InfInteger -> m a
lCalcEC c = lCalcC c

-- applyExtWithRt is simply serialC (defined below) since it is
-- the serial application of the parent root and the extension of the
-- final constraint. Only values in the paernt root may appear in the
-- extension (see X.680 section G.4.2.3).

lApplyExtWithRt :: (Eq a, L.Lattice a, L.IC a, Show a, MonadError [Char] m) =>
                   m a -> m a -> m a
lApplyExtWithRt a b = lSerialC a b

-- need to define encInt

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

lRootIntCons :: (L.Lattice (m a), L.IC a, MonadError [Char] m, Show a, L.Lattice a, Eq a) =>
                 m a -> [ESS L.InfInteger] -> m a
lRootIntCons x [] = x
lRootIntCons x (c:cs) = lRootIntCons (lEvalC c x) cs

lEvalC :: (L.Lattice (m a), L.IC a, MonadError [Char] m, Show a, L.Lattice a, Eq a) =>
          ESS L.InfInteger -> m a -> m a
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

lSerialC :: (MonadError [Char] m, Show a, L.Lattice a, L.IC a, Eq a) =>
            m a -> m a -> m a
lSerialC mx my =
   do a <- mx
      b <- my
      let la = L.getLower a
          ua = L.getUpper a
          lb = L.getLower b
          ub = L.getUpper b
          foobar
             | not (L.within a b)
                = throwError ("Constraint and parent type mismatch: " ++ show b ++ " is not within " ++ show a) -- Somehow we should prettyConstraint here
             | otherwise
                = return (L.serialCombine a b)
      foobar

lCalcC :: (MonadError [Char] m, L.IC a, L.Lattice (m a),
           L.Lattice a, Eq a, Show a) => Constr L.InfInteger -> m a
lCalcC (UNION u) = lCalcU u

-- Need to define unionC which returns the union of two
-- constraints

lCalcU :: (L.Lattice (m a), L.IC a, MonadError [Char] m,
           L.Lattice a, Eq a, Show a) => Union L.InfInteger -> m a
lCalcU (IC i) = lCalcI i
lCalcU(UC u i) = (lCalcU u) `L.ljoin` (lCalcI i)


lCalcI :: (L.IC a, MonadError [Char] m, L.Lattice (m a),
           L.Lattice a, Show a, Eq a) =>
          IntCon L.InfInteger -> m a
lCalcI (INTER i e) = (lCalcI i) `L.meet` (lCalcA e)
lCalcI (ATOM a)    = lCalcA a

lCalcA :: (L.IC a, MonadError [Char] m, L.Lattice (m a),
           L.Lattice a, Show a, Eq a) => IE L.InfInteger -> m a
lCalcA (E e) = lCalcE e

-- Note that the resulting constraint is always a contiguous set.

-- Need processCT to process the constraint implications of type
-- inclusion.
-- NOTE: Need to deal with illegal constraints resulting from
-- processCT

lCalcE :: (MonadError [Char] m, L.IC a, Show a, Eq a,
           L.Lattice a, L.Lattice (m a)) => Elem L.InfInteger -> m a
lCalcE (S (SV i)) = return (L.makeIC i i)
lCalcE (C (Inc t)) = lProcessCT t []
lCalcE (V (R (l,u))) = return (L.makeIC l u)



-- Note that a parent type does not inherit the extension of an
-- included type. Thus we use lRootIntCons on the included type.

lProcessCT :: (L.Lattice (m a), Show a, Eq a, L.Lattice a,
               L.IC a, MonadError [Char] m) => ASNType L.InfInteger -> [ESS L.InfInteger] -> m a
lProcessCT (BT INTEGER) cl = lRootIntCons L.top cl
lProcessCT (ConsT t c) cl  = lProcessCT t (c:cl)




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

lEncodeVisString :: (L.Lattice (m (L.ExtResStringConstraint L.ValidIntegerConstraint VisibleString)),
                     L.Lattice (m L.ValidIntegerConstraint),
                     MonadError [Char] m,
                     L.Lattice (m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)),
                     L.Lattice (m L.IntegerConstraint)) =>
                    [ESS VisibleString] -> VisibleString -> m BP.BitPut
lEncodeVisString [] vs = return (bitPutify (encodeVis vs))
lEncodeVisString cs vs
    = lEncVS effCon validCon vs
      where
        effCon :: (MonadError [Char] m, L.Lattice (m L.IntegerConstraint),
                   L.Lattice (m (L.ExtResStringConstraint L.IntegerConstraint VisibleString))) =>
                 m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)
        effCon = lSerialResEffCons L.top cs
        validCon :: (MonadError [Char] m, L.Lattice (m L.ValidIntegerConstraint),
                     L.Lattice (m (L.ExtResStringConstraint L.ValidIntegerConstraint VisibleString))) =>
                     m (L.ExtResStringConstraint L.ValidIntegerConstraint VisibleString)
        validCon = lSerialResEffCons L.top cs

-- The first case of encVS deals with non-per visible constraint.
-- If the constraint is non-per visible then we treat the value as
-- unconstrained.
-- NEED TO DEAL WITH CASE WHEN ROOT AND EXTENSION ARE DIFFERENT
-- CONSTRAINTS

stringMatch :: String -> String -> Bool
stringMatch [] s = True
stringMatch (f:r) s = elem f s && stringMatch r s


lEncVS :: (MonadError [Char] m) =>
          m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)
          -> m (L.ExtResStringConstraint L.ValidIntegerConstraint a)
          -> VisibleString
          -> m BP.BitPut
lEncVS m n v
    = do
        vsc <- m
        if L.extensible vsc
            then lEncExtVS m n v
            else lEncNonExtVS m n v


{-
A value is out of range if it is not within the constraint. This
includes the cases where either the size or PA constraint is
bottom which by default cannot be satisfied.
No constraint is represented by the lattice attribute top which is
the default value when generating an effective constraint.
-}

lEncNonExtVS :: (MonadError [Char] m) =>
                m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)
                -> m (L.ExtResStringConstraint L.ValidIntegerConstraint a)
                -> VisibleString
                -> m BP.BitPut
lEncNonExtVS m n vs@(VisibleString v)
    = do
        vsc <- m
        ok  <- n
        let rc = L.getRC vsc
            okrc = L.getRC ok
            sc = L.getSC rc
            L.Valid oksc = L.getSC okrc
            pac = L.getPAC rc
            emptyConstraint = rc == L.bottom
            noSC  = sc == L.top
            noPAC = pac == L.top
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength v
                  in l >= (L.lower x) && l <= (L.upper x) || inSizeRange rs
            inPA (VisibleString x)  = stringMatch v x
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | not noSC && not noPAC && inPA pac && inSizeRange oksc
                    = return (bitPutify (lEncodeVisSzF sc pac vs))
                | noSC && not noPAC && inPA pac
                    = return (bitPutify (lEncodeVisF pac vs))
                | noPAC && not noSC && inSizeRange oksc
                    = return (bitPutify (lEncodeVisSz sc vs))
                | otherwise
                    = throwError "Value out of range"
        foobar


lEncExtVS :: (MonadError [Char] m) =>
             m (L.ExtResStringConstraint L.IntegerConstraint VisibleString)
             -> m (L.ExtResStringConstraint L.ValidIntegerConstraint a)
             -> VisibleString
             -> m BP.BitPut
lEncExtVS m n vs@(VisibleString v)
    = do
        vsc <- m
        ok <- n
        let rc = L.getRC vsc
            ec = L.getEC vsc
            okrc = L.getRC ok
            okec = L.getEC ok
            rsc = L.getSC rc
            L.Valid okrsc = L.getSC okrc
            rpac = L.getPAC rc
            esc = L.getSC ec
            L.Valid okesc = L.getSC okec
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
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength v
                  in l >= (L.lower x) && l <= (L.upper x) || inSizeRange rs
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
                | noRPAC && inSizeRange okrsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSz rsc vs)
                | inPA rpac && inSizeRange okrsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSzF rsc rpac vs)
                | otherwise
                    = throwError "Value out of range"
            foobarEC
                | noESC && inPA epac
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (lEncodeVisF L.top vs)
                | noEPAC && inSizeRange okesc
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (encodeVis vs)
                | inPA epac && inSizeRange okesc
                    = return $ do BP.putNBits 1 (1::Int)
                                  bitPutify (lEncodeVisF L.top vs)
                | otherwise
                    = throwError "Value out of range"
            foobarBoth
                | not noRPAC && inPA rpac && not noRSC && inSizeRange okrsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSzF rsc rpac vs)
                | noRPAC && noEPAC && not noRSC && inSizeRange okrsc
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisSz rsc vs)
                | noRSC && noESC && not noRPAC && inPA rpac
                    = return $ do BP.putNBits 1 (0::Int)
                                  bitPutify (lEncodeVisF rpac vs)
                | noRPAC && noEPAC && not noESC && inSizeRange okesc
                     = return $ do BP.putNBits 1 (1::Int)
                                   bitPutify (encodeVis vs)
                | (not noRSC && inSizeRange okrsc && noRPAC && not noEPAC && inPA epac) ||
                  (not noRSC && inSizeRange okrsc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (not noESC && inSizeRange okesc && not noRPAC && inPA rpac) ||
                  (not noESC && inSizeRange okesc && noRPAC && not noEPAC && inPA epac) ||
                  (not noESC && inSizeRange okesc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (noRSC && noESC && ((noRPAC && not noEPAC && inPA epac) ||
                  (not noRPAC && not noEPAC && not (inPA epac) && inPA expac)))
                     =  return $ do BP.putNBits 1 (1::Int)
                                    bitPutify (lEncodeVisF L.top vs)
                | otherwise
                     = throwError "Value out of range"
        foobar

lEncodeVisSz :: (L.RS a) => L.IntegerConstraint -> a -> BitStream
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

fromPer :: (MonadError [Char] (t BG.BitGet), MonadTrans t) => ASNBuiltin a -> [ElementSetSpecs a] ->
                    t BG.BitGet a
fromPer t@INTEGER cl  = decodeInt cl

fromPer2 :: (MonadError [Char] (t BG.BitGet), MonadTrans t, L.Lattice (m L.IntegerConstraint),
             MonadError String m) => ASNBuiltin a -> [ElementSetSpecs a] -> m (t BG.BitGet a)
fromPer2 t@INTEGER cl = decodeInt2 cl

decodeInt [] = decodeUInt >>= \(L.V x) -> return (L.V (fromIntegral x))

decodeInt2 [] = error "you haven't done unconstrained decoding!"
decodeInt2 cs =
   lEitherTest2 parentRoot lc
   where
      lc         = last cs
      ic         = init cs
      parentRoot = lRootIntCons L.top ic

lEitherTest2 pr lc =
   lDecConsInt2 effRoot effExt
   where
      (effExt,b) = lApplyExt pr lc
      effRoot    = lEvalC lc pr

bitPutify :: BitStream -> BP.BitPut
bitPutify = mapM_ (BP.putNBits 1)

decodeUInt :: (MonadError [Char] (t1 BG.BitGet), MonadTrans t1) => t1 BG.BitGet L.InfInteger
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
                                   return (L.V rootLower)
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
                                                     return (L.V v)
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
