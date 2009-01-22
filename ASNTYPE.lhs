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

The module that hosts our Haskell representation of ASN.1 types is {\em ASNTYPE}.

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
classification alluded to above to be described using a single polymorphic and recursive
Haskell type which we call
{\em ASNType}. Note that in Haskell type names begin with an upper-case letter and
variable names begin with a lower-case letter. In the definition of {\em ASNType} the
name {\em a} represents a type variable which can be replaced by any type -- hence a
polymorphic type.
\begin{code}

data ASNType a where
    BuiltinType     :: ASNBuiltin a -> ASNType a
    ReferencedType  :: TypeReference -> ASNType a -> ASNType a
    ConstrainedType :: ASNType a -> SubtypeConstraint a -> ASNType a

\end{code}

Thus we can represent several types using the same interface. The keyword {\em data} introduces a new type identifier with the various forms that
values of the type can take listed below it. Thus an {\em ASNType} can be
\begin{itemize}
\item
a built-in type of type {\em ASNBuiltin} prefixed by the constructor {\em BuiltinType};
\item
a type reference of the type {\em TypeReference} and a {\em ASNType} prefixed by the constructor
{\em ReferencedType}. Note that a referenced type comes in various forms which we discuss
later in this paper; or
\item
a constrained type which is an {\em ASNType} associated with a constraint prefixed by
the constructor {\em ConstrainedType}. The constraint has a {\em SubtypeConstraint} type which
is described in section \ref{constraint}.
\end{itemize}

In table \ref{table1} we present some example ASN.1 types with their Haskell representations and types.
\begin{table}[h]
\caption{ASN.1 Types}
\label{table1}
\begin{tabular}{lll}
{\bf ASN.1 Type} & {\bf Haskell Representation} & {\bf Type} \\
{\tt BOOLEAN} & {\em BuiltinType BOOLEAN} & {\em ASNType Bool}\\
{\tt INTEGER} & {\em BuiltinType INTEGER} & {\em ASNType InfInteger}\\
{\tt INTEGER (1..4)} & {\em ConstrainedType}  & {\em ASNType InfInteger}\\
& {\em \hspace{0.5cm} (BuiltinType INTEGER) intCons} &
\end{tabular}
\end{table}

Note that {\em Bool} is the Haskell boolean type and {\em InfInteger} is our representation of an
integer type with named maximum and minimum values.
We have used the name {\em intCons} for an integer value range constraint to avoid presenting full
details of our constraint representation. This is described later in this paper.


\subsection{ASN.1 BuiltinType}
\label{asnbuiltin}

{\em ASNBuiltin} in common with {\em ASNType} is a parameterised algebraic type. However in this case we also
want to be able to assign an appropriate type to any of its constructors. In the previous section
we presented examples which used the {\em ASNBuiltin} values {\em BOOLEAN} and {\em INTEGER}. These have
different types that directly impact on the type of the {\em ASNType} value which uses them
in their construction. This type-based distinction is essential when encoding ASN.1 values -- the type
of the value to be encoded determines the encoding function that is used.
We discuss this further in section \ref{sequence}.

To achieve this constructor-specific type we need to use a {\em generalised algebraic data type} (GADT)
which assigns a (potentially different) type for each of the type's constructors, rather than
requiring each to have the same (albeit polymorphic) type as is the case with {\em ASNType}.
The GADT {\em ASNBuiltin} closely
resembles the production listed in section 16.2 of X.680. Note however that:
\begin{itemize}
\item
the character string types are represented individually without the need for another type
to represent restricted and unrestricted character strings; and
\item
the following ASN.1 types are not included in this specification:\\ {\tt EmbeddedPDVType},
{\tt ExternalType}, {\tt InstanceOfType}, {\tt ObjectClassFieldType},
{\tt ObjectIdentifierType}, {\tt RealType} and {\tt RelativeOIDType}.
\end{itemize}

\begin{code}

data ASNBuiltin a where
   BITSTRING       :: NamedBits -> ASNBuiltin BitString
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin InfInteger
   ENUMERATED      :: Enumerate a -> ASNBuiltin (ExactlyOne a SelectionMade)
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
   CHOICE          :: Choice a -> ASNBuiltin (ExactlyOne a SelectionMade)
   TAGGED          :: TagInfo -> ASNType a -> ASNBuiltin a

\end{code}

The {\em ASNBuiltin} type includes:
\begin{itemize}
\item
the constructors {\em NULL}, {\em BOOLEAN}, {\em INTEGER}, {\em OCTETSTRING} and the various
character string constructors which directly represent their associated ASN.1 built-in type. Each has a
different type which uses either the Haskell built-in equivalent of the ASN.1 type or, in the case of the
string types, new Haskell types to represent these types. Note that we have not included the possibility of
associating a named number list with an integer type since X.680 section 18.3 states that it is
{\em not significant in the definition of a type};
\item
the constructor {\em BITSTRING} requires the (possibly empty) collection of named bits to
construct a value of the bitstring type;
\item
the constructors {\em SEQUENCE} and {\em SET} require a {\em Sequence} input to specify the
particular type of sequence being represented. That is, different sequences may have different
types.
For example, a sequence constructed from an integer and a boolean has a
different type from one constructed from a couple of visible strings.
We describe the type {\em Sequence} in section \ref{sequence};
\item
the constructor {\em ENUMERATED} which requires an input that represents the particular
enumeration;
\item
the {\em SEQUENCEOF} and {\em SETOF} constructors which require the type of the individual
components to be provided as input. These could be any of the ASN.1 types (or any named type).
The return type for
{\em SEQUENCEOF} and {\em SETOF} is a list type (denoted {\em [a]}), which is Haskell's built-in
type for representing zero or more values of the same type;
\item
the {\em CHOICE} constructor which, because of the similarities of a choice type to a sequence type,
also requires an input that specifies the particular choices that are available. However, the
return type needs to emphasise that only one value may actually be used. This is achieved by using
a new type {\em ExactlyOne} which we describe later in this paper. This is also the approach used
for an enumerated type; and
\item
the {\em TAGGED} constructor which creates a tagged value from a tag and builtin type value.
\end{itemize}

We present in table \ref{ASN1Builtin} some examples of how we represent ASN.1 built-in types.

\begin{table}[h]
\caption{ASN.1 Builtin Types}
\label{ASN1Builtin}
\begin{tabular}{ll}
{\bf ASN.1 Builtin Type} & {\bf Haskell Representation}  \\
{\tt BOOLEAN} & {\em BOOLEAN}\\
{\tt INTEGER} & {\em INTEGER}\\
{\tt SEQUENCE \{\}} & {\em SEQUENCE Nil}\\
{\tt SEQUENCE \{a INTEGER, b BOOLEAN\} & {\em SEQUENCE }\\
& \hspace{0.2cm}{\em (AddComponent aComponent}\\
& \hspace{0.4cm}{\em (AddComponent bComponent Nil))}
\end{tabular}
\end{table}

Note that {\em aComponent} and {\em bComponent} are names assigned to
sequence components.Full details of our representation of sequences and their component types
including {\em aComponent} and {\em bComponent}
are presented in section \ref{sequence}.


The last built-in type example uses a value of the {\em Sequence} type which is described in
section \ref{sequence}. This is followed by descriptions of our represenations of the ASN.1 {\tt
ChoiceType}, {\tt EnumeratedType} and {\tt SequenceOfType}

\subsection{ASN.1 ReferencedType}
\label{constraint}
An ASN.1 referenced type is typically simply the type
reference component of a type assignment. However, since we require the compile-time type
checker to raise any type errors, we need to associate any type reference with its type.
For example\\
\\
{\em ReferencedType (Ref "T") (BuiltinType INTEGER)}\\
\\
represents a reference to the ASN.1 type {\tt IntegerType}. Although this appears simply to
add unnecessary complexity to the code, it allows us to faithfully pretty print ASN.1 types.

\subsection{ASN.1 ConstrainedType}
\label{constraint}

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
GeneralConstraint} with or without an exception. We have only implemented subtype contraints.

Now a {\tt SubtypeConstraint} can be non-extensible, extensible but as yet have no extension
additions, or be extensible with extension additions. Our type {\em Subtypeconstraint}
provides for each of these cases.

\begin{code}

data SubtypeConstraint a where
    RootOnly :: ConstraintSet a -> SubtypeConstraint a
    EmptyExtension :: ConstraintSet a -> SubtypeConstraint a
    NonEmptyExtension :: ConstraintSet a -> ConstraintSet a -> SubtypeConstraint a

\end{code}

The root and extension addition components of a subtype constraint are values of type
{\em ConstraintSet}. These are constraints that are specified as a combination of atomic
constraints. They are combined using set operations. At the top-most level a constraint is
either a union of sub-constraints or the complement of a constraint.

\begin{code}

data ConstraintSet a where
 UnionSet        :: Union a -> ConstraintSet a
 ComplementSet   :: Excl a  -> ConstraintSet a

\end{code}



\begin{code}

data Union a = IC (IntCon a) | UC (Union a) (IntCon a)

\end{code}

\begin{code}

newtype TypeReference = Ref {ref :: String}

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






\begin{code}

type NamedBits = [NamedBit]

data NamedBit = NB String Int

\end{code}
Definition of Constraint Type

\begin{code}
-- This current version of the constraint type has ignored exceptions (see X.680 45.6)

type SerialSubtypeConstraints a = [SubtypeConstraint a]

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
\end{code}

\subsection{ASN.1 SequenceType}
\label{sequence}

A sequence type is a (possibly heterogeneous) collection of component types. The normal approach in Haskell
when representing a collection of items is to use the built-in list type. However, each item of a
list {\em must} be
of the same Haskell type and thus is inappropriate for a sequence. Instead we use a new GADT {\em Sequence}
which is presented below. It has four constructors for building sequence types.
\begin{itemize}
\item
{\em EmptySequence} which is the empty sequence;
\item
{\em ExtensionMarker} which represents an extension marker and does not change the type of the sequence
since no new component types are added;
\item
{\em ExtensionAdditionGroup} which takes a (possibly empty) version number, an extension addition group
(represented as a sequence type) and the current sequence, and returns the new sequence possibly with
the new extension addition group.
An extension addition group is optional and thus we need to provide for the inclusion or not of this
component. This is achieved by using the Haskell type {\em Maybe};
\item
{\em AddComponent} which creates a new sequence type by adding a component type to an
existing sequence type.
\end{itemize}

\begin{code}
data Sequence a where
   EmptySequence            :: Sequence Nil
   ExtensionMarker          :: Sequence l -> Sequence l
   ExtensionAdditionGroup   :: VersionNumber -> Sequence a -> Sequence l
                                                -> Sequence (Maybe a :*: l)
   AddComponent             :: ComponentType a -> Sequence l
                                                -> Sequence (a:*:l)

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

The type {\em Nil} has one value {\em Empty} which is used as the starting point for the
creation of any sequence. The heterogeneous list {\em :*:} uses a constrctor of the same name
to build heterogeneous lists. The two declarations that begin with the keyword {\em instance}
are type class instatiations. A type class is a collection of types which allow common behaviour
as specified by their list of associated functions. The instantiations add types -- in this case {\em Nil} and {\em :*:} to type
classes -- in this case {\em Show}. Thus the function {\em show} can now be used with values
of the types {\em Nil} and {\em :*:}, which enables the printing of values of these types.

In table \ref{sequenceEqs} we present some illustrative example sequences and their types.

\begin{table}[h]
\caption{Example Sequences}
\label{sequenceEqs}
\begin{tabular}{ll}
{\bf Sequence} & {\bf Haskell Type}  \\
{\em AddComponent integerComp EmptySequence} & {\em Sequence (InfInteger :*: Nil)}\\
{\em AddComponent boolComp} & \\
\hspace{0.2cm} {\em (AddComponent stringComp EmptySequence)} & {\em Sequence (Bool :*: String :*: Nil)}\\
{\em AddComponent integerComp1} & \\
\hspace{0.2cm} {\em (ExtensionMarker &\\
\hspace{0.25cm} {\em (ExtensionAdditionGroup NoVersionNumber &\\
\hspace{0.3cm} {\em (AddComponent integerComp2 EmptySequence) &\\
\hspace{0.35cm} {\em EmptySequence))} & {\em Sequence (InfInteger :*: (Maybe (InfInteger :*: Nil):*: Nil))}
\end{tabular}
\end{table}
To avoid providing a full representation of sequence components we have given them names
such as {\em integerComp1}. We will later refer to the examples in table \ref{sequenceEqs}
as {\em sequence1}, {\em sequence2} and {\em sequence3} respectively.


It is clear that the type of a sequence depends on the number and type of components.
This explicit type information is required when encoding a sequence so that the appropriate
encoding function is is used on each component of a sequence.

Now continuing with the illustrative examples provided in table \ref{sequenceEqs} we can create
the following {\em ASNBuiltin} types.

\begin{itemize}
\item
{\em SEQUENCE sequence1} has type {\em InfInteger :*: Nil}.
\item
{\em SEQUENCE sequence2} has type {\em Bool :*: String :*: Nil}.
\item
{\em SEQUENCE sequence3} has type {\em InfInteger :*: (Maybe (InfInteger :*: Nil):*: Nil)}.
\end{itemize}

The component types of a sequence are represented by the GADT {\em ComponentType}. There are
four forms of component type.
\begin{itemize}
\item
a mandatory named type component created by {\em MandatoryComponent};
\item
an optional named type component created by {\em OptionalComponent}. Note that once agin we
have used the built-in Haskell type {\em Maybe} to represent that something is optional;
\item
a default named type component created by {\em DefaultComponent}. Here one also has to supply
the default value of this component if one is not provided with the sequence;
\item
components of an existing sequence type. This is created by {\em ComponentsOf}.
\end{itemize}

Note that we have added an extra constructor {\em ExtensionComponent} which deals with an extension
addition which is neither optional nor default. It returns a {\em Maybe} value since an
extension item may not be present in a sequence.

\begin{code}

data ComponentType a where
   MandatoryComponent   :: NamedType a -> ComponentType a
   OptionalComponent    :: NamedType a -> ComponentType (Maybe a)
   DefaultComponent     :: NamedType a -> a -> ComponentType (Maybe a)
   ComponentsOf         :: ASNType a   -> ComponentType a
   ExtensionComponent   :: NamedType a -> ComponentType (Maybe a)

data NamedType a where
   NamedType :: Name -> ASNType a -> NamedType a

\end{code}

Thus the components {\em aComponent} and {\em bComponent} used in table \ref{ASN1Builtin} are
defined as
\begin{itemize}
\item
{\em MandatoryComponent (NamedType "a" (BuiltinType INTEGER))} and
\item
{\em MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN))} respectively.
\end{itemize}


\subsection{ASN.1 ChoiceType}
\label{sequence}

The ASN.1 {\em ChoiceType} has similarities to the {\em SequenceType}. In effect it is a
sequence of optional components where exactly one must be used for any incarnation. We
therefore have chosen a Haskell representation which has significant similarities to our
representation of the {\tt SequenceType}.

We use a new GADT {\em Choice} which is presented below.

\begin{code}
data Choice a where
    EmptyChoice                     :: Choice Nil
    ChoiceExtensionMarker           :: Choice l -> Choice l
    ChoiceExtensionAdditionGroup    :: VersionNumber -> Choice l -> Choice l
    ChoiceOption                    :: NamedType a -> Choice l -> Choice (a:*:l)
\end{code}


It has four constructors for building choice types.
\begin{itemize}
\item
{\em EmptyChoice} which is the empty choice;
\item
{\em ChoiceExtensionMarker} which represents an extension marker and does not change the type of the choice
since no new component types are added. Note that Haskell requires a different name for this constructor than
the one used for a sequence in order to avoid type ambiguity when the constructors are used;
\item
{\em ChoiceExtensionAdditionGroup} whose semantics are different from the sequence {\em
ExtensionAdditionGroup} constructor. Here we are adding a collection of potential new choices
but only one may ever be used for a particular incarnation. Thus we are simply indicating the
presence of an extension addition group to aid pretty printing and version identification;
\item
{\em ChoiceOption} which adds a new choice option to the current collection of choices.
\end{itemize}


In order to enforce one and only one value for a choice the ASNBuiltin
constructor {\em CHOICE} returns a value of the type {\em ASNBuiltin (ExactlyOne a OneValue)}.

{\em ExactlyOne} is a type for heterogeneous lists (similar
to {\em Sequence}) except that it takes a second input which indicates
the number of actual values in the list. It has the following constructors:
\begin{itemize}
\item
{\em EmptyList} which is the base case for this type - the empty list. It has the type
{\em ExactlyOne Nil NoSelectionMade} where {\em NoSelectionMade} - a type with no associated values
- is a type indicating that no choice has yet been made.
\item
{\em AddAValue} which adds a value to a list.
Its return type is {\em ExactlyOne (a:*:l) SelectionMade)} indicating a choice has now been made.
{\em SelectionMade} is also a type with no associated values; and
\item
{\em AddNoValue} which adds no value (of the appropriate type -- hence the use
of the phantom type {\em NoValue a}) to a list. In this case the number of values in the
list is not incremented.
\end{itemize}

A phantom type is one in which a type variable appears only on the left hand side of the
type's definition. Thus a value of the type -- such as {\em NoValue} -- can match many
different types. We use this as a placeholder for the non-selected components of a choice (and
enumerated) type which will need to satisfy the various component types.

It is important to have the constructors {\em AddAValue} and {\em AddNoValue} so that there is
a match between the choice value and the choice type. That is, the overall choice value has the
appropriate type, and the particular choice of value has the required type.


\begin{code}

data ExactlyOne a l where
    EmptyList      :: ExactlyOne Nil NoSelectionMade
    AddAValue      :: a -> ExactlyOne l NoSelectionMade -> ExactlyOne (a:*:l) SelectionMade
    AddNoValue     :: NoValue a -> ExactlyOne l n -> ExactlyOne (a:*:l) n

data NoSelectionMade

data SelectionMade

data NoValue a = NoValue

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

instance Eq (ExactlyOne Nil SelectionMade) where
   _ == _ = True

instance (Eq a, Eq (ExactlyOne l SelectionMade)) => Eq (ExactlyOne (a:*:l) SelectionMade) where
   AddAValue   _ _ == AddNoValue _ _ = False
   AddNoValue _ _ == AddAValue _ _   = False
   AddNoValue _ xs == AddNoValue _ ys = xs == ys
   AddAValue x _ == AddAValue y _ = x == y

\end{code}

\subsection{ASN.1 EnumeratedType}
\label{enumerate}

An enumeration type is a collection of identifiers which are each implicitly or explicitly associated
with an integer. We use an algebraic type {\em EnumerationItem} to represent these two possible
cases. It has two constructors:
\begin{itemize}
\item
{\em Identifier} which constructs an enumeration item from a name. Any such item will be implicitly
assigned a distinct non-negative number; and
\item
{\em NamedNumber} which constructs an enumeration item from a name and a non-negative number
which must be distinct from any number already assigned to an {\em Identifier} or already in
existence in a {\em NamedNumber}.
\end{itemize}

The GADT {\em Enumerate} represents an enumeration built from {\em EnumerationItem}s. This
has three constructors:
\begin{itemize}
\item
{\em EmptyEnumeration} which represents an empty enumeration;
\item
{\em AddEnumeration} which adds an {\em EnumerationItem} to an existing enumeration; and
\item
{\em EnumerationExtensionMarker} which indicates the existence of an extension marker.
\end{itemize}

Note that an enumeration value is represented using a heterogeneous list of possible values.

\begin{code}

data EnumerationItem a where
    Identifier :: Name -> EnumerationItem Name
    NamedNumber :: Name -> Integer -> EnumerationItem Name

data Enumerate a where
    EmptyEnumeration            :: Enumerate Nil
    AddEnumeration              :: EnumerationItem a -> Enumerate l -> Enumerate (a:*:l)
    EnumerationExtensionMarker  :: Enumerate l -> Enumerate l

\end{code}

\subsection{SequenceOfType}


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


-- UNIVERSAL TAG FUNCTIONS
\begin{code}
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
