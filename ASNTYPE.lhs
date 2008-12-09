\section{Abstract Syntax Tree}
In this section we present our Haskell representation of the Abstract Syntax Notation One (ASN.1) \cite{ASN1}.
We assume that the reader is familiar with ASN.1 and has also had some experience with
programming languages. No prior knowledge of Haskell is required. We do not provide a tutorial
overview of Haskell, but, where necessary, include some commentary to aid the reading of the
enbedded code.

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
of potentially complex ASN.1 types. We describe how ASN.1 types can be created using our Haskell
representation. We do not describe here the creation of ASN.1 values and thus do not represent
ASN.1 value assignments. However, our representation of ASN.1 values are made explicit when
describing and illustrating the PER encoding of such values.

\subsection{ASN.1 Type}
\label{asntype}

ASN.1 types are categorised as follows:
\begin{itemize}
\item
a builtin type -- any of the standard ASN.1 types or a tagged type;
\item
a referenced type -- a (qualified or unqualified) type reference or a parameterised type (defined in X.683);
or
\item
a constrained type -- a type with a constraint.
\end{itemize}

We represent ASN.1 types using Haskell's algebraic data type mechanism which enables the
classification alluded to above to be described using a single Haskell type which we call {\tt ASNType}.
\begin{code}

data ASNType a where
    BuiltinType     :: ASNBuiltin a -> ASNType a
    ReferencedType  :: TypeReference -> ASNType a -> ASNType a
    ConstrainedType :: ASNType a -> SubtypeConstraint a -> ASNType a

\end{code}

{\tt ASNType} is a parameterised type so that we can distinguish between the various ASN.1
builtin types. The keyword {\tt data} introduces a new type identifier with the various forms that
values of the type can take listed below it. Thus an {\tt ASNType} value can be
\begin{itemize}
\item
a builtin type which we call {\tt ASNBuiltin} prefixed by the constructor {\tt BuiltinType};
\item
a type reference {\tt TypeReference} and an {\tt ASNType} prefixed by the constructor
{\tt ReferencedType}. Note that a referenced type has various incarnations which we discuss
later in this paper; or
\item
a constrained type which is an {\tt ASNType} value associated with a constraint prefixed by
the constructor {\tt ConstrainedType}. The constraint is called {\tt SubtypeConstraint} which
we will explain later in this document.
\end{itemize}

We present here some example ASN.1 types with their Haskell representations and types.
\begin{itemize}
\item
{\tt BOOLEAN} is represented as {\tt BuiltinType BOOLEAN} where {\tt BOOLEAN} is a value
of type {\tt ASNBuiltin Bool} (which is fully described in section \ref{asnbuiltin}) and has
the type {\tt ASNType Bool}. {\tt Bool} is the Haskell boolean type.
\item
{\tt INTEGER} is represented as {\tt BuiltinType INTEGER} and has the type {\tt ASNType
InfInteger}. {\tt InfInteger} is an integer type with named maximum and minimum values.
\item
{\tt INTEGER (1..4)} is represented as {\tt ConstrainedType (BuiltinType INTEGER)
intConstraint} where {\tt intConstraint} is an integer value range constraint. The
representation of constraints is described later in this paper. The type of this entity is
{\tt ASNType Integer}.
\end{itemize}

Note that {\tt ASNType} is a recursive type
since both a referenced type and a constrained type are built from an existing {\tt ASNType} value.

\subsection{ASN.1 BuiltinType}
\label{asnbuiltin}

{\tt ASNBuiltin} in common with {\tt ASNType} is a parameterised algebraic type. However in this case we also
want to be able to assign an appropriate type to any of its constructors. In section \ref{asntype} we
presented examples which used the {\tt ASNBuiltin} values {\tt BOOLEAN} and {\tt INTEGER}. These have
different types that directly influenced the type of the {\tt ASNType} value which used them
in their construction. This type-based distinction is essential when encoding ASN.1 values as
first described in section \ref{sequence}.

To achieve this constructor-specific type we need to use a {\em generalised algebraic data type} (GADT)
which assigns a (potentially different) type for each of the type's constructors, rather than
requiring each to have the same type. The GADT {\tt ASNBuiltin} closely
resembles the production listed in section 16.2 of X.680. Note that:
\begin{itemize}
\item
the character string types are represented individually without the need for another type
to represent restricted and unrestricted character strings; and
\item
the following types are not included in this specification: {\tt EmbeddedPDVType},
{\tt ExternalType}, {\tt InstanceOfType}, {\tt ObjectClassFieldType},
{\tt ObjectIdentifierType}, {\tt RealType} and {\tt RelativeOIDType}.
\end{itemize}

\begin{code}

data ASNBuiltin a where
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
   SEQUENCEOF      :: ASNType a -> ASNBuiltin [a]
   SET             :: Sequence a -> ASNBuiltin a
   SETOF           :: ASNType a -> ASNBuiltin [a]
   CHOICE          :: Choice a -> ASNBuiltin (ExactlyOne a OneValue)
   TAGGED          :: TagInfo -> ASNType a -> ASNBuiltin a

\end{code}

The {\tt ASNBuiltin} type includes:
\begin{itemize}
\item
the constructors {\tt NULL}, {\tt BOOLEAN}, {\tt INTEGER}, {\tt OCTETSTRING} and the various
character string constructors which directly represent their associated ASN.1 builtin type. Each has a
different type which uses either the Haskell builtin equivalent of the ASN.1 type or, in the case of the
string types, new Haskell types to represent these types. Note that we have not included the possibility of
associating a named number list with an integer type since to quote X.680 section 18.3 states that it is
{\em not significant in the definition of a type};
\item
the constructor {\tt BITSTRING} requires the (possibly empty) collection of named bits to
construct a value of the bitstring type;
\item
the constructors {\tt SEQUENCE} and {\tt SET} which require a {\tt Sequence} input to specify the
particular type of sequence being represented. That is, different sequences may have differenct types.
For example, a sequence constructed from an integer and a boolean value, has a
different type from one constructed from a couple of visible strings and another sequence of
booleans. We describe the type {\tt Sequence} in section \ref{sequence};
\item
the constructor {\tt ENUMERATE} which requires an input which represents the particular
enumeration;
\item
the {\tt SEQUENCEOF} and {\tt SETOF} constructors which require the type of the individual
components to be provided as input. These could be any of the ASN.1 types (or any named type).
The return type for
{\tt SEQUENCEOF} and {\tt SETOF} is a list type (denoted {\tt [a]}), which is Haskell's builtin
type for representing zero or more values of the same type;
\item
the {\tt CHOICE} constructor which, because of the similarities of a choice type to a sequence type,
also requires an input that specifies the particular choices that are available. However, the
return type needs to emphasise that only one value may actually be used. This is achieved by using
a new type {\tt ExactlyOne} which we describe later in this paper; and
\item
the {\tt TAGGED} constructor whcih creates a tagged value from a tag and builtin type value.
\end{itemize}

We present below some examples of how we represent ASN.1 types.

The builtin types {\tt BooleanType} and {\tt IntegerType} are represented as {\tt BuiltinType
BOOLEAN} and {\tt BuiltinType INTEGER} repectively. The {\tt SequenceType}
\begin{verbatim}
SEQUENCE {a INTEGER, b BOOLEAN}
\end{verbatim}
is represented as
\begin{verbatim}
BuiltinType
 (SEQUENCE
    (AddComponent (MandatoryComponent (NamedType "a" (BuiltinType INTEGER)))
       (AddComponent (MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN))) Nil)))
\end{verbatim}

We will leave illustrative examples of constrained types until we have described our
representation of ASN.1 constraints. An ASN.1 referenced type is typically simply the type
reference component of a type assignment. However, since we require the compile-time type
checker to raise any type errors, we need to associate any type reference with its type. Thus

\begin{verbatim}
ReferencedType (TypeRef "T") (BuiltinType INTEGER)
\end{verbatim}
represents a reference to the ASN.1 type {\tt IntegerType}. Although this appears simply to
add unnecessary complexity to the code, it allows us to faithfully pretty print ASN.1 types.

The last builtin type example uses a value of the {\tt Sequence} type which requires some explanation. This
will be followed by an explanation of our representation of the ASN.1 {\tt ChoiceType} and
{\tt SequenceOfType}

\subsection{ASN.1 SequenceType}
\label{sequence}

A sequence type is a (possibly heterogeneous) collection of component types. The normal approach in Haskell
when representing a collection of items is to use the builtin list type. However, each item of a list must be
of the same Haskell type and thus is inappropriate for a sequence. Instead we use a new GADT {\tt Sequence}
which is presented below. It has four constructors for building sequence types.
\begin{itemize}
\item
{\tt EmptySequence} which is the empty sequence;
\item
{\tt ExtensionMarker} which represents an extension marker and does not change the type of the sequence
since no new component types are added;
\item
{\tt ExtensionAdditionGroup} which takes a (possibly empty) version number, an extension addition group
(represented as a sequence type) and the current sequence and returns the new sequence with the extension
addition group {\em possibly} at the front.
An extension addition group is optional and thus we need to provide for the inclusion or not of this
component. This is achieved by using the Haskell type {\tt Maybe};
\item
{\tt AddComponent} which creates a new sequence type by adding a component type to the front of an
existing sequence type.
\end{itemize}

\begin{code}
data Sequence a where
   EmptySequence            :: Sequence Nil
   ExtensionMarker          :: Sequence l -> Sequence l
   ExtensionAdditionGroup   :: VersionNumber -> Sequence a -> Sequence l -> Sequence (Maybe a :*: l)
   AddComponent             :: ComponentType a -> Sequence l -> Sequence (a:*:l)

data VersionNumber = NoVersionNumber | Version Int
\end{code}

Note that we have created our own heterogeneous list type using the following algebraic types.

\begin{code}
data Nil = Empty
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs
\end{code}

Here are some illustrative example sequences and their types.
\begin{itemize}
\item
{\tt AddComponent} ...component of type {\tt Integer} {\tt Nil} has
type {\tt Sequence (Integer :*: Nil)}. We will refer to this sequence as {\tt sequence1}.
\item
{\tt AddComponent} ...component of type {\tt Bool} (AddComponent ...component of type {\tt
String} {\tt Nil} has type {\tt Sequence (Bool :*: String :*: Nil)}. We will refer to this
sequence as {\tt sequence2}.
\item
{\tt AddComponent} ...component of type {\tt (Integer :*: Nil)} {\tt (ExtensionMarker
(ExtensionAdditionGroup} ...component of type {\tt Integer} {\tt Nil))} has type
{\tt Sequence ((Integer :*: Nil) :*: (Maybe Integer) :*: Nil}. We will refer to this
sequence as {\tt sequence3}.
\end{itemize}



Thus the type of a sequence depends on the number and type of components. This explicit type
information is required because the encoding of a sequence (and for that matter any value)
depends on its actual type. That is, the function that
encodes a value of a builtin type {\tt toPER} takes a {\tt ASNBuiltin} type and a value of this type
(as well as some constraint information) and calls the appropriate encoding function which is determined
by the input type. The type of this function (which is defined in the module {\tt PER}) is

\begin{verbatim}
toPer :: ASNBuiltin a -> a -> SerialSubtypeConstraints a -> PerEncoding
\end{verbatim}

Now continuing with the illustrative examples provided above we can create two
{\tt ASNBuiltin} values as follows.

\begin{itemize}
\item
{\tt SEQUENCE sequence1} has type {\tt Integer :*: Nil}.
\item
{\tt SEQUENCE sequence2} has type {\tt Bool :*: Integer :*: Nil}.
\item
{\tt SEQUENCE sequence3} has type {\tt ((Integer :*: Nil) :*: Maybe Integer :*: Nil}.
\end{itemize}

The component types of a sequence are represented by the GADT {\tt ComponentType}. There are
four forms of component type.
\begin{itemize}
\item
a mandatory named type component created by {\tt MandatoryComponent};
\item
an optional named type component created by {\tt OptionalComponent}. Note that once agin we
have used the builtin Haskell type {\tt Maybe} to represent that something is optional;
\item
a default named type component created by {\tt DefaultComponent}. Here one also has to supply
the default value of this component if one is not provided with the sequence;
\item
components of an existing sequence type. This is created by {\tt ComponentsOf}.
\end{itemize}

Note that we have added an extra constructor {\tt ExtensionComponent} which deals with an extension
addition which is neither optional nor default. It returns a {\tt Maybe} value since an
extension item may not be present in a sequence.

\begin{code}

data ComponentType a where
   MandatoryComponent   :: NamedType a -> ComponentType a
   OptionalComponent    :: NamedType a -> ComponentType (Maybe a)
   DefaultComponent     :: NamedType a -> a -> ComponentType (Maybe a)
   ComponentsOf         :: ASNType a   -> ComponentType a -- these will typically be referenced
                                                    -- types
   ExtensionComponent   :: NamedType a -> ComponentType (Maybe a)

data NamedType a where
   NamedType :: Name -> ASNType a -> NamedType a

\end{code}

\subsection{ASN.1 ChoiceType}
\label{sequence}

The ASN.1 {\tt ChoiceType} has similarities to the {\tt SequenceType}. In effect it is a
sequence of optional components where exactly one must be used for any incarnation. We
therefore have chosen a Haskell representation which has significant similarities to our
representation of the {\tt SequenceType}.

We use a new GADT {\tt Choice} which is presented below. It has four constructors for building choice types.
\begin{itemize}
\item
{\tt EmptyChoice} which is the empty choice;
\item
{\tt ChoiceExtensionMarker} which represents an extension marker and does not change the type of the sequence
since no new component types are added. Note that Haskell requires a different name for this constructor than
the one used for a sequence in order to avoid type ambiguity when the constructors are used;
\item
{\tt ChoiceExtensionAdditionGroup} whose semantics are different from the sequence {\tt
ExtensionAdditionGroup} constructor. Here we are adding a collection of potential new choices
but only one may ever be used for a particular incarnation. Thus we are simply indicating the
presence of an extension addition group to aid pretty printing and version identification;
\item
{\tt ChoiceOption} which adds a new choice option to the current collection of choices.
\end{itemize}

\begin{code}
data Choice a where
    EmptyChoice                     :: Choice Nil
    ChoiceExtensionMarker           :: Choice l -> Choice l
    ChoiceExtensionAdditionGroup    :: VersionNumber -> Choice l -> Choice l
    ChoiceOption                    :: NamedType a -> Choice l -> Choice (a:*:l)
\end{code}


In order to enforce one and only one value for a choice the ASNBuiltin
constructor CHOICE returns a value of the type {\tt ASNBuiltin (ExactlyOne a (S Z))}.

{\tt ExactlyOne} is a type for heterogeneous lists (similar
to {\tt Sequence}) except that it takes a second input which indicates
the number of actual values in the list. It has the following constructors:
\begin{itemize}
\item
{\tt EmptyList} is the base case for this type - the empty list. It has the type
{\tt ExactlyOne Nil ZeroValues} where {\tt ZeroValues} is a type indicating no values.
\item
{\tt AddAValue} which adds a value to a list.
Its return type is {\tt ExactlyOne (a:*:l) OneValue)} indicating that the list now
has one value; and
\item
{\tt NoAddAValue} which adds no value (of the appropriate type -- hence the use
of the phantom type {\tt Phantom a}) to a list. In this case the number of values in the
list is not incremented.
\end{itemize}

It is important to have the constructors {\tt AddAValue} and {\tt AddNoValue} so that there is
a match between the choice value and the choice type. That is, the overall choice value has the
appropriate type, and the particulat choice of value has the required type.


\begin{code}

data ExactlyOne a l where
    EmptyList      :: ExactlyOne Nil ZeroValues
    AddAValue      :: a -> ExactlyOne l ZeroValues -> ExactlyOne (a:*:l) OneValue
    AddNoValue     :: Phantom a -> ExactlyOne l n -> ExactlyOne (a:*:l) n

data ZeroValues

data Increment n

type OneValue = Increment ZeroValues

data Phantom a = NoValue

instance Show (ExactlyOne Nil n) where
   show _ = "EmptyExactlyOne"

instance (Show a, Show (ExactlyOne l n)) => Show (ExactlyOne (a:*:l) n) where
   show (AddAValue x _ ) = show x
   show (AddNoValue _ xs) = show xs

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys

instance Eq (ExactlyOne Nil OneValue) where
   _ == _ = True

instance (Eq a, Eq (ExactlyOne l OneValue)) => Eq (ExactlyOne (a:*:l) OneValue) where
   AddAValue   _ _ == AddNoValue _ _ = False
   AddNoValue _ _ == AddAValue _ _   = False
   AddNoValue _ xs == AddNoValue _ ys = xs == ys
   AddAValue x _ == AddAValue y _ = x == y

\end{code}


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



\begin{code}

data TypeReference = Ref TypeRef

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

data SubtypeConstraint a = RE (Constr a) | EXT (Constr a) | EXTWITH (Constr a) (Constr a)

type SerialSubtypeConstraints a = [SubtypeConstraint a]

data Constr a = UNION (Union a) | ALL (Excl a)

data Union a = IC (IntCon a) | UC (Union a) (IntCon a)

data IntCon a = INTER (IntCon a) (IE a) | ATOM (IE a)

data Excl a = EXCEPT (Elem a)

data IE a = E (Elem a) | Exc (Elem a) (Excl a)

data Elem a = S (SV a) | C (CT a) | V (VR a) | SZ (Sz a) | P (PA a) | IT (IS a)

data SV a = SingleValue a => SV a

data CT a = ContainedSubtype a => Inc (ASNType a)

data VR a = ValueRange a => R (a,a)

data Sz a = SizeConstraint a => SC (SubtypeConstraint InfInteger)

data PA a = PermittedAlphabet a => FR (SubtypeConstraint a)

--IS to be completed for multiple type constraints
data IS a = InnerType a => WC (SubtypeConstraint a) | WCS

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

data ConType i = ConType {conType :: i}
    deriving (Show, Eq)

data ExtBS i = ExtBS i i Bool
    deriving (Show, Eq)


data ResStringConstraint a i = ResStringConstraint a i
    deriving (Show,Eq)

data ExtResStringConstraint a = ExtResStringConstraint a a Bool
    deriving (Show, Eq)

-- UNIVERSAL TAG FUNCTIONS

getCTI :: ComponentType a -> TagInfo
getCTI (MandatoryComponent (NamedType _  (BuiltinType (TAGGED t ct)))) = t
getCTI (MandatoryComponent (NamedType _  t))             = getTI t
getCTI (ExtensionComponent (NamedType _  (BuiltinType (TAGGED t ct))))   = t
getCTI (ExtensionComponent (NamedType _ t))                = getTI t
getCTI (OptionalComponent (NamedType _  (BuiltinType (TAGGED t ct))))  = t
getCTI (OptionalComponent (NamedType _  t))              = getTI t
getCTI (DefaultComponent (NamedType _  (BuiltinType (TAGGED t ct))) d) = t
getCTI (DefaultComponent (NamedType _  t) d)             = getTI t

getTI :: ASNType a -> TagInfo
getTI (BuiltinType t) = getBuiltinTI t
getTI (ConstrainedType t _) = getTI t
getTI (ReferencedType r t) = getTI t

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
getCTags EmptyChoice                            = []
getCTags (ChoiceExtensionMarker xs)             = getCTags xs
getCTags (ChoiceExtensionAdditionGroup vn xs)   = getCTags xs
getCTags (ChoiceOption (NamedType n (BuiltinType (TAGGED t a))) xs)
        = t : getCTags xs
getCTags (ChoiceOption (NamedType n a) xs)
        = getTI a : getCTags xs

\end{code}
