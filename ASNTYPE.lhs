%if False

\begin{code}

{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
                -XScopedTypeVariables
#-}

\end{code}

%endif

\begin{code}

module ASNTYPE where

import Language.ASN1 hiding (Optional, BitString, PrintableString, IA5String,
                ComponentType(Default), NamedType, OctetString, VisibleString, NULL)
import Data.Word

\end{code}

An ASN.1 module is typically populated by {\em inter alia} a collection of type assignments which associate
upper-case letter prefixed identifiers (formally known as type references) with ASN.1 types. Type references
begin with an upper-case letter to distinguish them from value references which are used to identify
ASN.1 values. These type references are then used to specify other types enabling a shorthand representation
of potentially complex ASN.1 types.

ASN.1 types are categorised as follows:
\begin{itemize}
\item
a built-in type -- any of the standard ASN.1 types or a tagged type;
\item
a referenced type -- a (qualified or unqualified) type reference or a parameterised type (defined in X.683);
or
\item
a constrained type -- a type with a constraint.
\end{itemize}

We represent ASN.1 types using Haskell's algebraic data type mechanism which enables the
classification alluded to above to be described using a single type. Thus {\tt ASNType} is
defined as
\begin{code}

data ASNType a where
    BT    :: ASNBuiltin a -> ASNType a
    RT    :: ReferencedType -> ASNType a
    ConsT :: ASNType a -> ESS a -> ASNType a

\end{code}

where the keyword {\tt data} introduces a new type identifier, and the various forms that
values of the type can take are listed below. Thus an {\tt ASNType} value can be
\begin{itemize}
\item
a built-in type which we call {\tt ASNBuiltin} prefixed by the constructor {\tt BT};
\item
a referenced type {\tt ReferencedType} prefixed by {\tt RT}; or
\item
a constrained type which is simply an {\tt ASNType} value associated with a constraint prefixed by
{\tt ConsT}. The constraint is called {\tt ESS} which we will explain later in this document.

This type is parameterised by the various ASN.1 builtin types. It is a recursive type
since a constrained type is built from an {\tt ASNType} value.

We also use an algebraic type to represent the ASN.1 built-in types. However, in this case it
is a {\em generalised algebraic data type} (GADT) which allows us to specify appropriate
return types for each class of values of the type, rather than requiring each to have the same
type, as was the case for {\tt ASNType}. The GADT {\tt ASNBuiltin} closely resembles the
production listed in section 16.2 of X.680. Note that:
\begin{itemize}
\item
the character string types are represented individually without the need for another type
to represent restricted and unrestricted character strings; and
\item
the following types are not incldued in this specification: {\tt EmbeddedPDVType},
{\tt ExternalType}, {\tt InstanceOfType}, {\tt ObjectClassFieldType},
{\tt ObjectIdentifierType}, {\tt RealType} and {\tt RelativeOIDType}.
\end{itemize}

\begin{code}

data ASNBuiltin a where
   TYPEASS         :: TypeRef -> Maybe TagInfo -> ASNBuiltin a -> ASNBuiltin a -- to be changed
   BITSTRING       :: NamedBits -> ASNBuiltin BitString
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin InfInteger
   ENUMERATED      :: Enumerate a -> ASNBuiltin a
   OCTETSTRING     :: ASNBuiltin OctetString
   PRINTABLESTRING :: ASNBuiltin PrintableString
   IA5STRING       :: ASNBuiltin IA5String
   VISIBLESTRING   :: ASNBuiltin VisibleString
   NUMERICSTRING   :: ASNBuiltin NumericString
   UNIVERSALSTRING :: ASNBuiltin UniversalString
   BMPSTRING       :: ASNBuiltin BMPString
   NULL            :: ASNBuiltin Null
   SEQUENCE        :: Sequence a -> ASNBuiltin a
   SEQUENCEOF      :: ASNBuiltin a -> ASNBuiltin [a]
   SET             :: Sequence a -> ASNBuiltin a
   SETOF           :: ASNBuiltin a -> ASNBuiltin [a]
   CHOICE          :: Choice a -> ASNBuiltin (HL a (S Z))
   TAGGED          :: TagInfo -> ASNType a -> ASNBuiltin a

\end{code}

The {\tt ASNBuiltin type} includes:
\begin{itemize}
\item
the constructors {\tt NULL}, {\tt BOOLEAN}, {\tt INTEGER}, {\tt OCTETSTRING} and the various
character string constructors which directly represent their associated ASN.1 builtin type;
\item
the constructor {\tt BITSTRING} requires the (possibly empty) collection of named bits to
construct a value of the bitstring type;
\item
the constructors {\tt SEQUENCE} and {\tt SET} which require a {\tt Sequence} input to specify the
particular type of sequence being represented. That is, the sequence input describes the particular sequence being
used since, for example, a sequence constructed from an integer and a boolean value, has a
different type from one constructed from a couple of visible strings and another sequence of
booleans;
\item
the constructor {\tt ENUMERATE} also requires an input which represents the particular
enumeration;
\item
the {\tt SEQUENCEOF} and {\tt SETOF} constructors which require the type of the individual
components to be provided as input. These could be any of the builtin types and thus the type
{\tt ASNBuiltin, in common with the type {\tt ASNType}, is a recursive type. The return type for
{\tt SEQUENCEOF} and {\tt SETOF} is a list type (denoted {\tt [a]}) since values of these
types may include zero or more component values;
\item
the {\tt CHOICE} constructor which, because of the similarities of a choice type to a sequence type,
also requires an input that specifies the particular choices that are available. However, the
return type needs to emphasise that only one value may actually be used. This is achieved by using
a new type {\tt HL} which we describe later in this paper; and
\item
the {\tt TAGGED} constructor whcih creates a tagged value from a tag and builtin type value.
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



X.680 16.1

Type ::= BuiltinType | ReferencedType | ConstrainedType

\begin{code}

-- SOME REFERENCE THOUGHTS!!!!

data TRef = forall a. Show a =>  TRef (ASNType a)


refList = [("a", TRef (BT INTEGER)), ("b", TRef (BT VISIBLESTRING)),("c",  TRef (BT BOOLEAN))]

getType :: String -> [(String,TRef)] -> TRef
getType nm [] = error ""
getType nm (f:r) = if fst f == nm then snd f
                                  else getType nm r

{-

No good because cannot directly define a recursive function over these structures.
trefList
    = ("a", (BT INTEGER)):*: (("b", (BT VISIBLESTRING)) :*: (("c", (BT BOOLEAN)) :*: Nil))



getType x (f:*:r)
    = if x == fst f
        then snd f
        else getType x r
getType x _ = error "No such type reference"


-}

--



data ReferencedType = Ref TypeRef

data Null = Null
    deriving Show

data InfInteger = NegInf | Val Integer | PosInf
    deriving (Show, Ord, Eq)

instance Bounded InfInteger where
   minBound = NegInf
   maxBound = PosInf

instance Num InfInteger where
   PosInf + _ = PosInf
   _ + PosInf = PosInf
   NegInf + _ = NegInf
   _ + NegInf = NegInf
   (Val x) + (Val y) = Val (x + y)
   PosInf - _ = PosInf
   _ - PosInf = NegInf
   NegInf - _ = NegInf
   _ - NegInf = PosInf
   (Val x) - (Val y) = Val (x - y)
   fromInteger v = Val v
\end{code}


-- Type aliases
\begin{code}

type TagInfo    = (TagType, TagValue, TagPlicity)
type TypeRef    = String
type Name       = String

\end{code}

Type Classes which make explicit the (not necessarily PER-visible) subtypes associated with the ASN.1 types.

See X.680 (07/2002) Section 47.1 Table 9

\begin{code}

class SingleValue a

instance SingleValue BitString
instance SingleValue InfInteger
instance SingleValue VisibleString
instance SingleValue PrintableString
instance SingleValue NumericString
instance SingleValue UniversalString
instance SingleValue BMPString
instance SingleValue IA5String

class ContainedSubtype a

instance ContainedSubtype BitString
instance ContainedSubtype InfInteger
instance ContainedSubtype VisibleString
instance ContainedSubtype PrintableString
instance ContainedSubtype NumericString
instance ContainedSubtype UniversalString
instance ContainedSubtype BMPString
instance ContainedSubtype IA5String


class ValueRange a

instance ValueRange IA5String
instance ValueRange PrintableString
instance ValueRange NumericString
instance ValueRange VisibleString
instance ValueRange UniversalString
instance ValueRange BMPString
instance ValueRange InfInteger


class PermittedAlphabet a

instance PermittedAlphabet IA5String
instance PermittedAlphabet PrintableString
instance PermittedAlphabet NumericString
instance PermittedAlphabet VisibleString
instance PermittedAlphabet UniversalString
instance PermittedAlphabet BMPString



class SizeConstraint a

instance SizeConstraint [a]
instance SizeConstraint IA5String
instance SizeConstraint PrintableString
instance SizeConstraint NumericString
instance SizeConstraint VisibleString
instance SizeConstraint UniversalString
instance SizeConstraint BMPString
instance SizeConstraint BitString
instance SizeConstraint OctetString

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
   EAG     :: Sequence a -> Sequence l -> Sequence (Maybe a :*: l)
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
   CTCompOf    :: ASNBuiltin a   -> ComponentType a -- these will typically be referenced
                                                    -- types

data NamedType a where
   NamedType :: Name -> ASNType a -> NamedType a

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
Its return type is HL (a:*:l) (S Z) indicating that the list now
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
    NamedNumber :: Name -> Integer -> EnumerationItem Name

data Enumerate a where
    NoEnum      :: Enumerate Nil
    EnumOption  :: EnumerationItem a -> Enumerate l -> Enumerate ((Maybe a):*:l)
    EnumExt     :: Enumerate l -> Enumerate l

\end{code}




\begin{code}

type NamedBits = [NamedBit]

data NamedBit = NB String Int

\end{code}
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

data Sz a = SizeConstraint a => SC (ESS InfInteger)

data PA a = PermittedAlphabet a => FR (ESS a)

--IS to be completed for multiple type constraints
data IS a = InnerType a => WC (ESS a) | WCS

-- Type constraint (constraining an open type) to be done (47.6)
-- Pattern constraint to be done.

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
newtype VisibleString = VisibleString {visibleString :: String}
    deriving (Eq, Show)
newtype UniversalString = UniversalString {universalString :: String}
    deriving (Eq, Show)
newtype BMPString = BMPString {bmpString :: String}
    deriving (Eq, Show)

type BitStream = [Int]
type Octet = Word8
type OctetStream = [Octet]

-- Some constraint-related types

data IntegerConstraint = IntegerConstraint {lower :: InfInteger, upper :: InfInteger}
   deriving (Show, Eq)

-- ValidIntegerConstraint is used for the validity testing of a value against a constraint. Thus, unlike an
-- effective constraint (which is used to produce encoding in a small number of bits) and is always a contiguous
-- set of values, this type represents the true result of set combinations of constraints which may be non-contiguous.

data ValidIntegerConstraint = Valid [IntegerConstraint]
    deriving (Show, Eq)


data ConType i = ConType i
    deriving (Show, Eq)

data ExtBS i = ExtBS i i Bool
    deriving (Show, Eq)


data ResStringConstraint a i = ResStringConstraint a i
    deriving (Show,Eq)

data ExtResStringConstraint a = ExtResStringConstraint a a Bool
    deriving (Show, Eq)

-- UNIVERSAL TAG FUNCTIONS

getCTI :: ComponentType a -> TagInfo
getCTI (CTMandatory (NamedType _  (BT (TAGGED t ct)))) = t
getCTI (CTMandatory (NamedType _  t))             = getTI t
getCTI (CTExtMand (NamedType _  (BT (TAGGED t ct))))   = t
getCTI (CTExtMand (NamedType _ t))                = getTI t
getCTI (CTOptional (NamedType _  (BT (TAGGED t ct))))  = t
getCTI (CTOptional (NamedType _  t))              = getTI t
getCTI (CTDefault (NamedType _  (BT (TAGGED t ct))) d) = t
getCTI (CTDefault (NamedType _  t) d)             = getTI t

getTI :: ASNType a -> TagInfo
getTI (BT t) = getBuiltinTI t
getTI (ConsT t _) = getTI t
getTI (RT r) = error "TO DO!"

getBuiltinTI :: ASNBuiltin a -> TagInfo
getBuiltinTI BOOLEAN            = (Universal, 1, Explicit)
getBuiltinTI INTEGER            = (Universal,2, Explicit)
getBuiltinTI (BITSTRING _)      = (Universal, 3, Explicit)
getBuiltinTI OCTETSTRING        = (Universal, 4, Explicit)
getBuiltinTI NULL               = (Universal, 5, Explicit)
getBuiltinTI PRINTABLESTRING    = (Universal, 19, Explicit)
getBuiltinTI IA5STRING          = (Universal,22, Explicit)
getBuiltinTI VISIBLESTRING      = (Universal, 26, Explicit)
getBuiltinTI NUMERICSTRING      = (Universal, 18, Explicit)
getBuiltinTI UNIVERSALSTRING    = (Universal, 28, Explicit)
getBuiltinTI BMPSTRING          = (Universal, 30, Explicit)
getBuiltinTI (SEQUENCE s)       = (Universal, 16, Explicit)
getBuiltinTI (SEQUENCEOF s)     = (Universal, 16, Explicit)
getBuiltinTI (SET s)            = (Universal, 17, Explicit)
getBuiltinTI (SETOF s)          = (Universal, 17, Explicit)
getBuiltinTI (CHOICE c)         = (minimum . getCTags) c

getCTags :: Choice a -> [TagInfo]
getCTags NoChoice                     = []
getCTags (ChoiceExt xs)               = getCTags xs
getCTags (ChoiceEAG xs)               = getCTags xs
getCTags (ChoiceOption (NamedType n (BT (TAGGED t a))) xs)
        = t : getCTags xs
getCTags (ChoiceOption (NamedType n a) xs)
        = getTI a : getCTags xs
\end{code}
