\section{Abstract Syntax Tree}
\todo{Be consistent with tense -- we present, we create ...}

In this section we present our Haskell representation of the Abstract Syntax Notation One (ASN.1) \cite{ASN1}.
We assume that the reader is familiar with ASN.1 and has also had some experience with
programming languages. No prior knowledge of Haskell is required. We do not provide a tutorial
overview of Haskell, but, where necessary, include some commentary to aid the reading of the
embedded code. We believe that Haskell, as a strongly-typed language, is a natural language for implementing 
ASN.1, a type-based notation. 

%if False
\begin{code}

{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
                -XScopedTypeVariables
#-}

{-# LANGUAGE NoMonomorphismRestriction #-}

\end{code}

%endif

The module that hosts our Haskell representation of ASN.1 types is {\em ASNTYPE}. It uses the
type {\em Word8} which is defined in the imported library module {\em Data.Word}.

\begin{code}

module ASNTYPE where

import Data.Word
import List

\end{code}

An ASN.1 module is typically populated by {\em inter alia} a collection of type assignments which associate
upper-case letter prefixed identifiers (formally known as type references) with ASN.1 types. Type references
begin with an upper-case letter to distinguish them from value references which are used to identify
ASN.1 values. These type references are then used to specify other types enabling a shorthand representation
of potentially complex ASN.1 types. We describe how ASN.1 types can be created using our Haskell
representation. We do not describe here the creation of ASN.1 values and thus do not describe our representation of 
ASN.1 value assignments. However, once ASN.1 types are implemented their associated values are represented 
quite naturally as in the following example. 

\begin{verbatim}
aBooleanType :: ASNType Bool
aBooleanType = BuiltinType BOOLEAN

aBooleanValue :: Bool
aBooleanValue = True 
\end{verbatim}

Note that type of the value matches the type of the parameter of {\em ASNType}. Note also that although by using Haskell we can check the validity of a value against its type, this is only the case for unconstrained types. For constrained types we can typecheck the value against the (unconstrained type) but then required the PER ecnoding function to check that the value satisfies the stated constraint.

We present below our representation of the ASN.1 record structure of X.691, Annex A, section A.2.1.
\todo{Pretty-printing example and representation of constraints}

\begin{code}
personnelRecord
    = BuiltinType (TAGGED (Application, 0, Implicit) (BuiltinType (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name))) .*.
                      (MandatoryComponent (NamedType "title" (BuiltinType (TAGGED (Context, 0, Explicit) (BuiltinType VISIBLESTRING))))) .*.
                        (MandatoryComponent (NamedType "number" (ReferencedType (Ref "EmpNumber") empNumber))) .*.
                          (MandatoryComponent (NamedType "dateOfHire" (BuiltinType (TAGGED (Context, 1, Explicit) (ReferencedType (Ref "Date") date))))) .*.
                            (MandatoryComponent (NamedType "nameOfSpouse" (BuiltinType (TAGGED (Context, 2, Explicit) (ReferencedType (Ref "Name") name))))) .*.
                              (DefaultComponent (NamedType "children" 
                                (BuiltinType (TAGGED (Context, 3, Implicit) (BuiltinType (SEQUENCEOF (ReferencedType (Ref "ChildInformation") childInformation)))))) []) .*.
                                            empty))))


personnelRecord31
    = BuiltinType (TAGGED (Application, 0, Implicit) (BuiltinType (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name31))) .*.
                      (MandatoryComponent (NamedType "title" (BuiltinType (TAGGED (Context, 0, Explicit) (BuiltinType VISIBLESTRING))))) .*.
                        (MandatoryComponent (NamedType "number" (ReferencedType (Ref "EmpNumber") empNumber31))) .*.
                          (MandatoryComponent (NamedType "dateOfHire" (BuiltinType (TAGGED (Context, 1, Explicit) (ReferencedType (Ref "Date") date31))))) .*.
                            (MandatoryComponent (NamedType "nameOfSpouse" (BuiltinType (TAGGED (Context, 2, Explicit) (ReferencedType (Ref "Name") name31))))) .*.
                              (OptionalComponent (NamedType "children" 
                                (BuiltinType (TAGGED (Context, 3, Implicit) 
					     (ConstrainedType (BuiltinType (SEQUENCEOF (ReferencedType (Ref "ChildInformation") childInformation31)))
					     	(EmptyExtension (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (2,2)))))))))))))))))))) .*.
                                                empty))))
 

childInformation
    = BuiltinType
                (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name))) .*.
                        (MandatoryComponent (NamedType "dateOfBirth" (BuiltinType (TAGGED (Context, 0, Explicit) (ReferencedType (Ref "Date") date))))) .*.
                                            empty))

childInformation31
    = BuiltinType
                (SET
                    ((MandatoryComponent (NamedType "name" (ReferencedType (Ref "Name") name31))) .*.
                        (MandatoryComponent (NamedType "dateOfBirth" (BuiltinType (TAGGED (Context, 0, Explicit) (ReferencedType (Ref "Date") date31))))) .*.
			   (ExtensionMarker 
			     ((OptionalComponent (NamedType "sex" 
			        (BuiltinType (TAGGED (Context, 1, Implicit) 
			           (BuiltinType (ENUMERATED (AddEnumeration (NamedNumber "male" 1) 
					        (AddEnumeration (NamedNumber "female" 2)
						(AddEnumeration (NamedNumber "unknown" 3)
						 EmptyEnumeration))))))))) .*.
                                                  empty))))


name
    = BuiltinType (TAGGED (Application, 1, Implicit) (BuiltinType (SEQUENCE
                    ((MandatoryComponent (NamedType "givenName" (ReferencedType (Ref "NameString") nameString))) .*.
                        (MandatoryComponent (NamedType "initial" 
				      (ConstrainedType (ReferencedType (Ref "NameString") nameString)
	    			        (RootOnly (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (1,1)))))))))))))))))) .*.
                            (MandatoryComponent (NamedType "familyName" nameString)) .*. empty))))

name31
    = BuiltinType (TAGGED (Application, 1, Implicit) (BuiltinType (SEQUENCE
                    ((MandatoryComponent (NamedType "givenName" (ReferencedType (Ref "NameString") nameString31'))) .*.
                        (MandatoryComponent (NamedType "initial" 
				      (ConstrainedType (ReferencedType (Ref "NameString") nameString31')
	    			        (RootOnly (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion (NoIntersection 
                      				  (ElementConstraint (V (R (1,1)))))))))))))))))) .*.
                            (MandatoryComponent (NamedType "familyName" nameString31')) .*. (ExtensionMarker  empty)))))


empNumber = BuiltinType (TAGGED (Application, 2, Implicit) (BuiltinType INTEGER))

empNumber31 = ConstrainedType (BuiltinType (TAGGED (Application, 2, Implicit) (BuiltinType INTEGER)))
	      	(EmptyExtension (UnionSet (NoUnion (NoIntersection
	              				  (ElementConstraint (V (R (0,9999))))))))	      
	      		      	      

date = ConstrainedType
        (BuiltinType (TAGGED (Application, 3, Implicit) (BuiltinType VISIBLESTRING)))
        (RootOnly (UnionSet (NoUnion 
           (IntersectionMark (NoIntersection
                                (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion 
                                   (NoIntersection 
                                      (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))
				(ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion 
				   (NoIntersection 
				      (ElementConstraint (V (R (8,8)))))))))))))))

date31 = ConstrainedType
        (BuiltinType (TAGGED (Application, 3, Implicit) (BuiltinType VISIBLESTRING)))
        (RootOnly (UnionSet (NoUnion 
           (IntersectionMark (NoIntersection
                                (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion 
                                   (NoIntersection 
                                      (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))
				(ElementConstraint (SZ (SC (NonEmptyExtension (UnionSet (NoUnion 
				   (NoIntersection 
				      (ElementConstraint (V (R (8,8)))))))
                                       (UnionSet (NoUnion 
				        (NoIntersection 
				       (ElementConstraint (V (R (9,20)))))))
                                       ))))))))

nameString = ConstrainedType 
               (BuiltinType VISIBLESTRING)
	       (RootOnly (UnionSet (NoUnion 
                 (IntersectionMark (NoIntersection
                                      (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion (NoIntersection 
                                               (ElementConstraint (S (SV (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])))))))))))))
				      (ElementConstraint (SZ (SC (RootOnly (UnionSet (NoUnion
				               (NoIntersection (ElementConstraint (V (R (1,64)))))))))))))))

nameString31 = ConstrainedType 
               (BuiltinType VISIBLESTRING)
	       (RootOnly (UnionSet (NoUnion 
                 (IntersectionMark (NoIntersection
                                      (ElementConstraint (P (FR (RootOnly (UnionSet (NoUnion (NoIntersection
                                                                                         -- FIXME: This is semantically the same
                                                                                         -- FIXME: but will not render the same
                                                                                         -- FIXME: as the example 
                                               (ElementConstraint (S (SV (VisibleString (['a'..'z'] ++ ['A'..'Z'] ++ ['-','.'])))))))))))))
				      (ElementConstraint (SZ (SC (EmptyExtension (UnionSet (NoUnion
				               (NoIntersection (ElementConstraint (V (R (1,64)))))))))))))))

nameString31' =
   ConstrainedType (BuiltinType VISIBLESTRING)
                   (RootOnly (UnionSet (NoUnion
                     ((NoIntersection (ElementConstraint (P (FR (RootOnly (UnionSet x)))))) /\
                      (NoIntersection (ElementConstraint (SZ (SC (EmptyExtension (UnionSet y))))))))))
      where
         x = (singletonUnion . VisibleString $ ['a'..'z']) \/
             (singletonUnion . VisibleString $ ['A'..'Z']) \/
             (singletonUnion . VisibleString $ "-.")

         y = singletonUnion' (1, 64)



singletonIntersection :: (SingleValue a) => a -> Intersections a
singletonIntersection = NoIntersection . ElementConstraint . S . SV

-- FIXME: Hopefully temporary as we should be able to unify these somehow
singletonIntersection' :: (ValueRange a) => (a, a) -> Intersections a
singletonIntersection' = NoIntersection . ElementConstraint . V . R

singletonUnion :: (SingleValue a) => a -> Unions a
singletonUnion = NoUnion . singletonIntersection

-- FIXME: Hopefully temporary as we should be able to unify these somehow
singletonUnion' :: (ValueRange a) => (a, a) -> Unions a
singletonUnion' = NoUnion . singletonIntersection'

infixl 5 \/
(\/) :: Unions a -> Unions a -> Unions a
x \/ (NoUnion y) = UnionMark x y

infixl 6 /\
(/\) :: Intersections a -> Intersections a -> Intersections a
x /\ (NoIntersection y) = IntersectionMark x y

\end{code}

Here is our representation of the record value presented in X.691, Annex A, section A.2.2.

\begin{code}
pr = emp :*: t :*: num :*: hiredate :*: sp :*: Just cs :*: Empty

emp = empGN :*: empI :*: empFN :*: Empty

empGN = VisibleString "John"

empFN = VisibleString "Smith"

empI = VisibleString "P"

t = VisibleString "Director"

num = Val 51

hiredate = VisibleString "19710917"

sp = spGN :*: spI :*: spFN :*: Empty

spGN = VisibleString "Mary"

spI  = VisibleString "T"

spFN = VisibleString "Smith"

cs = [c1,c2]

c1 = ((c1GN :*: (c1I :*: (c1FN :*: Empty))) :*: (c1BD :*: (c1Sex :*: Empty)))
c2 = ((c2GN :*: (c2I :*: (c2FN :*: Empty))) :*: (c2BD :*: (c2Sex :*: Empty)))

c1GN = VisibleString "Ralph"
c1I  = VisibleString "T"
c1FN = VisibleString "Smith"
c1BD = VisibleString "19571111"
c1Sex = Nothing

c2GN = VisibleString "Susan"
c2I  = VisibleString "B"
c2FN = VisibleString "Jones"
c2BD = VisibleString "19590717"
c2Sex = Just (AddEnumeration (NamedNumber "female" 2) EmptyEnumeration)
\end{code}

\subsection{ASN.1 Type}
\label{asntype}

The top-level ASN.1 type, which is simply called {\tt Type}, encompasses all ASN.1 types. Each type is
classified as:
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
classification alluded to above to be described using a single, polymorphic and recursive
Haskell type which we call
{\em ASNType}. Note that in Haskell type names begin with an upper-case letter and
variable names begin with a lower-case letter. In the definition of {\em ASNType} the
name {\em a} represents a type variable which can be replaced by any type -- hence it is a
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
in section \ref{reference}; or
\item
a constrained type which is an {\em ASNType} associated with a constraint prefixed by
the constructor {\em ConstrainedType}. The constraint has a {\em SubtypeConstraint} type which
is described in section \ref{constraint}. Note that {\em ASNType} and {\em SubtypeConstraint}
have the same parameter which enforces a matching -- at a type-level -- of the type and
its constraint.
\end{itemize}

In table \ref{table1} we present some example ASN.1 types with their Haskell representations and
the type of the Haskell representation.
\begin{table}[h]
\caption{ASN.1 Types}
\label{table1}
\begin{tabular}{lll}
{\bf ASN.1 Type} & {\bf Haskell Representation} & {\bf Type} \\
{\tt BOOLEAN} & {\em BuiltinType BOOLEAN} & {\em ASNType Bool}\\
{\tt INTEGER} & {\em BuiltinType INTEGER} & {\em ASNType InfInteger}\\
{\tt INTEGER (1..4)} & {\em ConstrainedType}  & {\em ASNType InfInteger}\\
& {\em \hspace{0.2cm} {\em BuiltinType INTEGER) intCons} &
\end{tabular}
\end{table}

Note that {\em Bool} is the Haskell boolean type and {\em InfInteger} is our representation of an
integer type with named maximum and minimum values.
We have used the name {\em intCons} for an integer value range constraint to avoid presenting full
details of our constraint representation. Full details of how we represent constraints are
provided in section \ref{constraint}.


\subsection{ASN.1 BuiltinType}
\label{ASNBuiltin}

{\em ASNBuiltin} in common with {\em ASNType} is a parameterised algebraic type. However in this case we also
want to be able to assign an appropriate type to any of its constructors. In the previous section
we presented examples which used the {\em ASNBuiltin} values {\em BOOLEAN} and {\em INTEGER}. These have
different types that directly impact on the type of the {\em ASNType} value which uses them
in their construction. This type-based distinction is essential when encoding ASN.1 values -- the type
of the value to be encoded determines the encoding function that is used.
We discuss this in detail when we describe our PER encoding functions.

To achieve this constructor-specific type we need to use a {\em generalised algebraic data type} (GADT)
which assigns a (potentially different) type for each of the type's constructors, rather than
requiring each to have the same (albeit polymorphic) type, as is the case with {\em ASNType}.
The GADT {\em ASNBuiltin} closely
resembles the production listed in section 16.2 of X.680. Note however that:
\begin{itemize}
\item
the character string types are represented directly without the need for an intermediate type
which distinguishes the restricted and unrestricted character strings. We currently only
represent a subset of the restricted character strings -- the known-multiplier
character string types; and
\item
the following ASN.1 types are not included in this specification:\\ {\tt EmbeddedPDVType},
{\tt ExternalType}, {\tt InstanceOfType}, {\tt ObjectClassFieldType},
{\tt ObjectIdentifierType}, {\tt RealType} and {\tt RelativeOIDType}.
\end{itemize}

\todo{How do we deal with automatic tagging?}

\begin{code}

data ASNBuiltin a where
   BITSTRING       :: NamedBits -> ASNBuiltin BitString
   BOOLEAN         :: ASNBuiltin Bool
   INTEGER         :: ASNBuiltin InfInteger
   ENUMERATED      :: Enumerate -> ASNBuiltin Enumerate
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
   CHOICE          :: Choice a
                        -> ASNBuiltin (ExactlyOne a SelectionMade)
   TAGGED          :: TagInfo -> ASNType a -> ASNBuiltin a

\end{code}
\todo{SEQUENCEOF and SETOF should have ASNTYPE or NamedType as input -- see X.680 25.1}

The {\em ASNBuiltin} type includes several constructors which we describe in the following
subsections. We have categorised the constructors as nullary - they are values of the type - and
non-nullary where they require at least one input to construct a value of the type.

\subsubsection{ASNBuiltin Nullary Constructors}

The nullary constructors {\em NULL}, {\em BOOLEAN}, {\em INTEGER}, {\em OCTETSTRING} and the various
character string constructors directly represent their associated ASN.1 built-in type.
Note that we have not included the possibility of associating a named
number list with an integer type since X.680 section 18.3 states that it is {\em not
significant in the definition of a type}.
Each constructor has a different type as indicated by the replacement of the parameter {\em a} with a concrete Haskell
type. The only Haskell built-in type that is used is {\em Bool}. Our type {\em Null} represents
nullness with a single value also called {\em Null}.

\begin{code}

data Null = Null
    deriving Show

\end{code}

The expression {\em deriving Show}
indicates that the type is being implicitly added to the built-in type class {\em Show}. A type class is simply a
collection of types typically with an explicit collection of associated functions, operators
and/or values. For example, any value of a {\em Show} type may be converted to its printable form
using a function {\em show}. This enables the overloading of the function, operator or value
names of a type class. For example, each type of the type class {\em Show} has the previously mentioned function
called {\em show}. This is not a single polymorphic function, but a collection of individually
defined functions which share the same name. This is similar to the type of polymorphism
common to object-oriented programming languages.

The type {\em InfInteger} is our integer type which is Haskell's {\em Integer} type 
augmented with maximum and minimum values. This
is also added to the types classes -- {\em Show}, {\em Eq} the equality testing class, and {\em
Ord} which hosts the comparison operators -- but is also being explicitly added to the type
classes {\em Bounded} and {\em Num}. This is indicated by the keyword {\em instance} and
requires the explicit implementation of the type class's entities. {\em Bounded} has two
values {\em minBound} and {\em maxBound} and {\em Num} includes the arithmetic operators.
\begin{code}

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
   (Val x) - (Val y) = Val (x-y)
   NegInf * NegInf = PosInf
   _ * NegInf = NegInf
   NegInf * _ = NegInf
   PosInf * _ = PosInf
   _ * PosInf = PosInf
   (Val x) * (Val y) = Val (x*y)
   fromInteger x = Val x

\end{code}


The restricted character string types and octetstring types are represented by
new Haskell types. They are each introduced by the keyword {\em newtype}.
This is used in place of {\em data} when one wants a type which is the same as an existing
type but is recognised as distinct from the existing type by the type system. Thus one is simply
wrapping an existing type in a constructor to
enable type distinction. Each new type includes a function for accessing the value wrapped in
the constructor. For example, the function {\em iA5String} converts an {\em IA5String} value
into a string.

Note that the {\em BitString} type mimics the type {\em BitStream} which is simply another
name for a list of integers. This is indicated by the keyword {\em type} which does not
introduce a new type, but simply declares an alias for an existing type. Similarly
the {\em OctetString} type mimics the type {\em OctetStream} which is a list of {\em Octet}s,
an alias for the Haskell type {\em Word8}.

\begin{code}

newtype BitString = BitString {bitString :: BitStream}
    deriving (Eq, Show)

type BitStream = [Int]

newtype OctetString = OctetString {octetString :: OctetStream}
    deriving (Eq, Show)

type Octet = Word8
type OctetStream = [Octet]

newtype IA5String = IA5String {iA5String :: String}
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

\end{code}

\subsubsection{The Non-Nullary Constructors}

The constructor {\em BITSTRING} requires a (possibly empty) collection of named bits to
construct a bitstring type.

\begin{code}

type Name       = String
data NamedBit = NB Name Int
type NamedBits = [NamedBit]

\end{code}

The constructors {\em SEQUENCE} and {\em SET} require a {\em Sequence} input to specify the
particular type of sequence or set being represented. That is, different sequences may have different
types. For example, a sequence constructed from an integer and a boolean has a
different type from one constructed from a couple of visible strings.
We describe the type {\em Sequence} in section \ref{sequence}. Note that the return type just uses the parameter
of the {\em Sequence} type since a sequence value will have the parameter's type.
\todo{Do we need to explain this?}

The {\em SEQUENCEOF} and {\em SETOF} constructors require the type of the individual
components to be provided as input. These could be any of the ASN.1 types (or any named type).
The return type for
{\em SEQUENCEOF} and {\em SETOF} is a list type (denoted {\em [a]}), which is Haskell's built-in
type for representing zero or more values of the same type.

The {\em CHOICE} constructor, because of the similarities of a choice type to a sequence type,
also requires an input that specifies the particular choices that are available. However, the
return type needs to emphasise that only one value may actually be used. This is achieved by using
a new type {\em ExactlyOne} which we describe in section \ref{choice}. This is also the approach used
for an enumerated type. The constructor {\em ENUMERATED} requires an input that represents the particular
enumeration of type {\em Enumerate}. This type is described in section \ref{enumerate}. 
Finally the {\em TAGGED} constructor creates a tagged value from an ASN.1 tag and
a built-in type.

\begin{code}

type TagInfo    = (TagType, TagValue, TagPlicity)

data TagType = Universal | Application | Context | Private
   deriving (Eq,Show,Enum,Ord)

type TagValue = Integer

data TagPlicity = Implicit | Explicit
   deriving (Eq,Show,Ord)

\end{code}

We present in table \ref{ASN1built-in} some examples of how we represent ASN.1 built-in types.
\todo{Should we show some values here as well?}
\begin{table}[h]
\caption{ASN.1 built-in Types}
\label{ASN1built-in}
\begin{tabular}{ll}
{\bf ASN.1 built-in Type} & {\bf Haskell Representation}  \\
{\tt BOOLEAN} & {\em BOOLEAN} \\
{\tt INTEGER} & {\em INTEGER}\\
{\tt SEQUENCE \{\}} & {\em SEQUENCE Nil}\\
{\tt SEQUENCE \{a INTEGER, b BOOLEAN\}} & {\em SEQUENCE}\\
& \hspace{0.2cm}{\em (AddComponent aComponent}\\
& \hspace{0.4cm}{\em (AddComponent bComponent Nil))}
\end{tabular}
\end{table}

Note that {\em aComponent} and {\em bComponent} are names assigned to
sequence components. Full details of our representation of sequences,
including the type {\em Sequence}, and their component types
including {\em aComponent} and {\em bComponent} are presented in section \ref{sequence}.
This is followed by descriptions of our representations of the ASN.1 {\tt
ChoiceType} and {\tt EnumeratedType}.

\subsection{ASN.1 ReferencedType}
\label{reference}
\todo{NEED A FULL EXPLANATION HERE -- SEE X.680}
An ASN.1 referenced type is typically simply the type
reference component of a type assignment.

\begin{code}

newtype TypeReference = Ref {ref :: String}

\end{code}


However, since we require the compile-time type
checker to raise any type errors, we need to associate any type reference with its type.

\todo{Is this the only way to do this?}
\todo{How often are we going to use type references?}
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

We implement both of these cases using the same approach. That is, a {\tt SETOF} or {\tt SEQUENCEOF} type associated with a constraint implies that the constraint
is applied to the collection. To constrain an element type of these collections we simply use a constrained type as the argument of {\tt SETOF} or {\tt SEQUENCEOF}.

\todo{Why is SizeConstraint singled out in X.680 45.5?}

A {\tt Constraint} is either a {\tt SubtypeConstraint} or a {\tt
GeneralConstraint} with or without an exception. We have only implemented subtype contraints
and have not implemented exceptions (X.680 clause 49).

A {\tt SubtypeConstraint} can be non-extensible, extensible but as yet have no extension
additions, or be extensible with extension additions. Our type {\em SubtypeConstraint}
provides for each of these cases and this type and other types specified in this section mimic the 
type assignments presented in X.680 section 46. It is a parameterised type so that constraint types can 
match the type with which they are associated as mentioned in section \ref{asntype}.

\begin{code}

data SubtypeConstraint a = RootOnly (ElementSetSpec a)
                            | EmptyExtension (ElementSetSpec a)
                            | NonEmptyExtension (ElementSetSpec a) (ElementSetSpec a)

\end{code}

The root and extension addition components of a subtype constraint are values of type
{\em ElementSetSpec}. These are constraints that are specified as a set combination of
various elemental constraints. At the top-most level a constraint is either a union of
sub-constraints or the complement of a constraint (everything except some stated constraint).

\begin{code}

data ElementSetSpec a = UnionSet (Unions a) | ComplementSet (Exclusions a)

\end{code}

The component constraints of a union are intersections of constraints which in turn are either element constraints
or the set difference of element constraints. 

\begin{code}

data Unions a = NoUnion (Intersections a) | UnionMark (Unions a) (Intersections a)
data Exclusions a = EXCEPT (Element a)
data Intersections a
    = NoIntersection (IntersectionElements a) | IntersectionMark (Intersections a) (IntersectionElements a)
data IntersectionElements a
    = ElementConstraint (Element a) | ExclusionConstraint (Element a) (Exclusions a)

\end{code}

There are various kinds of element constraint. There are eight atomic constraints listed as 
ASN.1 {\tt SubtypeElements}. Each of these may be 
applied to a known collection of the ASN.1 types as specified in table 9 in section 49.1 of X.680. 
In addition, an element constraint may be a parenthesised {\tt ElementSetSpec} or {\tt ObjectSetElememts} as described 
in X.681. We have not implemented the last of these.

\todo{Some overall explanation why we are not implementing objects.} 

Our representation of each of the atomic element constraints are presented below the
definition of the type {\em Element}. We manage the association of an element
constraint with the appropriate ASN.1 types (as listed in table 9) by using a collection of new Haskell type classes. For
example, 

\begin{itemize}
\item
the {\em ValueRangeConstraint} may only be applied to types which are members of the
type class {\em ValueRange} as indicated by {\em ValueRange a $=>$} in the definition of the
{\em ValueRangeConstraint} type, and 
\item
the instance declarations for the {\em ValueRange} class indicate that 
{\em InfInteger} type and the various restricted character strings types are the only members of this type class.
\end{itemize}

Note that each type class is simply used for membership purposes and thus does not have any
associated methods. That is, the type classes restrict the set of the types to which a constraint may be applied. For example, a {\tt PermittedAlphabet} 
constraint may only be applied to a restricted character string type (since we haven't implemented the object descriptor type). 

We do not currently support the constraint {\tt TypeConstraint} which is only applied to an open type and thus
only of use with information object classes which are not part of this implementation. Neither do
we support the constraint {\tt PatternConstraint} which imposes a regular expression-based constraint on restricted
character string types.

\todo{The parent and included type in a contained subtype application should be the same. Our type system allows SETs and SEQUENCEs to be used 
interchangeably (and SETOF etc.).} 
\todo{Do we really need the parenthesis case -- for unambiguous parsing?}


\begin{code}

data Element a = S (SingleValueConstraint a) | C (ContainedSubtypeConstraint a)
                 | V (ValueRangeConstraint a) | P (PermittedAlphabetConstraint a)
                 | SZ (SizeConstraint a) | IT (InnerTypeConstraints a)
		 | Paren (ElementSetSpec a)


data SingleValueConstraint a = SingleValue a => SV a

data ContainedSubtypeConstraint a = ContainedSubtype a => Inc (ASNType a)

data ValueRangeConstraint a = ValueRange a => R (a,a)

data SizeConstraint a = Size a => SC (SubtypeConstraint InfInteger)

data PermittedAlphabetConstraint a = PermittedAlphabet a => FR (SubtypeConstraint a)

data InnerTypeConstraints a = InnerType a => WC (SubtypeConstraint a) | WCS


class SingleValue a

instance SingleValue BitString
instance SingleValue Bool
instance SingleValue InfInteger
instance SingleValue Null
instance SingleValue VisibleString
instance SingleValue PrintableString
instance SingleValue NumericString
instance SingleValue UniversalString
instance SingleValue BMPString
instance SingleValue IA5String
instance SingleValue a => SingleValue (ExactlyOne a SelectionMade)

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



class Size a

instance Size [a]
instance Size IA5String
instance Size PrintableString
instance Size NumericString
instance Size VisibleString
instance Size UniversalString
instance Size BMPString
instance Size BitString
instance Size OctetString

class InnerType a

instance InnerType (Choice a)
instance InnerType  (Sequence a)
instance InnerType [a]

\end{code}

We have now completed the implementation of the constraints defined in X.680.
In the following section we provide some types which are required in the generation and
processing of constraints. 

\subsection{Constraint Processing Types}

ASN.1 type constraints can be applied in series. We represent the collection of these constraints
using a list type which we call {\em SerialSubtypeConstraints}. It is a parameterised type because as mentioned previously the types of the constraint
and the ASN.1 type to which it is being applied must be the same.

\begin{code}
type SerialSubtypeConstraints a = [SubtypeConstraint a]
\end{code}

Now there are two types of constraints that may be generated:
\begin{itemize}
\item
the effective constraint which is used when PER-encoding an ASN.1 value. Only constraints that are applied to the appropriate type and that are PER-visible 
are used in the generation of the effective constraint. Table 9 in section 47.1 of X.680 summarizes which subtype elements can be applied to which
parent types. The PER-visible constraints are presented in
in section 9.3 of X.691.
\item
the validity-testing constraint. This uses all applicable subtype elements.
\end{itemize}

Thus any type which has at least one applicable subtype element needs a Haskell type to represent a constraint. We present these types in the following
sections.

\subsubsection{BooleanType Constraint}

{\em BooleanConstraint} is the type for a validity-testing {\tt BooleanType} constraint --
there is no effective {\tt BooleanType} constraint since this type has no PER-visible constraints.

\begin{code}

data BooleanConstraint = BooleanConstraint [Bool]
                                                 deriving (Show, Eq)

\end{code}

\subsubsection{IntegerType Constraints}

{\em IntegerConstraint} is the type for effective integer constraints. These
are contiguous sets of values and thus can be represented using a pair of values which
indicate the lower and upper limits of the range. In constrast {\em ValidIntegerConstraint} is
the type which represents the actual elements of a set combination of constraints which are
typically non-contiguous. These are required to test the validity of a value. Since they are
non-contiguous we represent their values as a list of contiguous sets.

We also introduce another type {\em IntegerConstraintType} which is an enumerated type with
three values: {\em Constrained}, {\em SemiConstrained} and {\em Unconstrained}. These values
are used to classify a constraint when encoding an integer. We have also implemented the
function {\em constraintType} which tests the form of a constraint and allocates the
appropriate value of the type {\em IntegerConstraintType}.

These functions and the type are used in the encoding of integer values as specified in section
\ref{intEnc}.

\begin{code}

data IntegerConstraint = IntegerConstraint {lower :: InfInteger, upper :: InfInteger}
   deriving (Show, Eq)

data ValidIntegerConstraint = Valid [IntegerConstraint]
    deriving (Show, Eq)


data IntegerConstraintType =
   Constrained     |
   SemiConstrained |
   UnConstrained

constraintType :: IntegerConstraint -> IntegerConstraintType
constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained

unconstrained,semiconstrained,constrained :: IntegerConstraint -> Bool
unconstrained x     = (lower x) == minBound
semiconstrained x   = (upper x) == maxBound
constrained x       = not (unconstrained x || semiconstrained x)

\end{code}

\subsubsection{EnumeratedType Constraints}

{\em EnumeratedConstraint} is the type for a validity-testing {\tt EnumeratedType} constraint --
there is no effective {\tt EnumeratedType} constraint since this type has no PER-visible
constraints.

An enumerated constraint is represented as a list of enumeration items.

\todo{Need to explain this.}

\begin{code}

data EnumeratedConstraint = EnumeratedConstraint [Integer]
                             deriving (Show, Eq)

\end{code}

\subsubsection{Restricted String Type Constraints}

The type {\em ResStringConstraint} represents the distinct components --
the permitted alphabet constraint and the size constraint -- of a root or extension
constraint of a restricted character string type. It is a polymorphic type to allow for the
various restricted character string types. {\em ExtensibleConstraint} supports the
combination of root and extension constraints. The boolean component indicates whether an
extension constraint exists.

\begin{code}

data ResStringConstraint a i = ResStringConstraint a i
    deriving (Show,Eq)

data ExtensibleConstraint i = ExtensibleConstraint i i Bool
    deriving (Show, Eq)

\end{code}

\todo{Need to explain why only mention extensible constraints here -- why not for integer type? Also more detail required regarding the parameters and why no 
type for BITSTRING and OCTETSTRING}

\subsection{ASN.1 SequenceType}
\label{sequence}
\todo{Position with type entries}
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
(represented as a {\em Sequence'} type) and the current sequence, and returns the new sequence possibly with
the new extension addition group. We use the {\em Sequence'} type to restrict the possible
components of an extension addition group;
An extension addition group is optional and thus we need to provide for the inclusion or not of this
component. This is achieved by using the Haskell type {\em Maybe};
\item
{\em AddComponent} which creates a new sequence type by adding a component type to an
existing sequence type.
\end{itemize}

\begin{code}
infixr .*.

class Sequences f where
    (.*.) :: ComponentType a -> f l -> f (a :*: l)
    empty :: f Nil
 
instance Sequences Sequence where
    (.*.) = AddComponent
    empty = EmptySequence
 
instance Sequences Sequence' where
    (.*.) = AddComponent'
    empty = EmptySequence'

infixr ...

class Sequences f => ExtensibleSequences f where
    (...) :: f l -> f l
    
instance ExtensibleSequences Sequence where 
    (...) = ExtensionMarker


data Sequence a where
   EmptySequence            :: Sequence Nil
   ExtensionMarker          :: Sequence l -> Sequence l
   ExtensionAdditionGroup   :: VersionNumber -> Sequence' a -> Sequence l
                                                -> Sequence (Maybe a :*: l)
   AddComponent             :: ComponentType a -> Sequence l
                                                -> Sequence (a:*:l)

data Sequence' a where
   EmptySequence'           :: Sequence' Nil
   AddComponent'            :: ComponentType a -> Sequence' l
                                                -> Sequence' (a:*:l)

makeSequence :: Sequence' a -> Sequence a
makeSequence EmptySequence' = EmptySequence
makeSequence (AddComponent' c s) = AddComponent c (makeSequence s)

data VersionNumber = NoVersionNumber | Version Int
\end{code}

Note that we have created our own heterogeneous list type using the following algebraic types.

\begin{code}
data Nil = Empty

infixr 5 :*:
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys
\end{code}

The type {\em Nil} has one value {\em Empty} which is used as the starting point for the
creation of any sequence. The heterogeneous list {\em :*:} uses a constructor of the same name
to build heterogeneous lists. We have added the type to the type classes {\em Show} and {\em Eq}
to enable the printing of values and equality testing.

In table \ref{sequenceEqs} we present some illustrative example sequences and their types.

\begin{table}[h]
\caption{Example Sequences}
\label{sequenceEqs}
\begin{tabular}{ll}
{\bf Sequence} & {\bf Haskell Type}  \\
{\em AddComponent integerComp} & \\
\hspace{0.2cm}{\em EmptySequence} & {\em Sequence (InfInteger :*: Nil)}\\
{\em AddComponent boolComp} & \\
\hspace{0.2cm} {\em (AddComponent stringComp} & \\
\hspace{0.4cm} {\em EmptySequence)} & {\em Sequence (Bool :*: String :*: Nil)}\\
{\em AddComponent integerComp1} & \\
\hspace{0.2cm} {\em (ExtensionMarker} &\\
\hspace{0.25cm} {\em (ExtensionAdditionGroup NoVersionNumber} &\\
\hspace{0.3cm} {\em (AddComponent integerComp2 EmptySequence)} &\\
\hspace{0.35cm} {\em EmptySequence))} & {\em Sequence (InfInteger :*:}\\
& \hspace{0.1cm} {\em (Maybe (InfInteger :*: Nil):*: Nil))}
\end{tabular}
\end{table}
To avoid providing a full representation of sequence components we have given them names
such as {\em integerComp1}.

It is clear that the type of a sequence depends on the number and type of components.
This explicit type information is required when encoding a sequence so that the appropriate
encoding function is used on each component of a sequence.
Continuing with the illustrative examples provided in table \ref{sequenceEqs} -- and refering
to them as {\em sequence1}, {\em sequence2} and {\em sequence3} respectively -- we can create
the {\em ASNBuiltin} types presented in table \ref{ASNSeqs}.

\begin{table}[h]
\caption{ASNBuiltin Sequences}
\label{ASNSeqs}
\begin{tabular}{ll}
{\bf Sequence} & {\bf Haskell Type}  \\
{\em SEQUENCE sequence1} & {\em InfInteger :*: Nil}\\
{\em SEQUENCE sequence2} & {\em Bool :*: String :*: Nil}\\
{\em SEQUENCE sequence3} & {\em InfInteger :*: (Maybe (InfInteger :*: Nil):*: Nil)}
\end{tabular}
\end{table}

The component types of a sequence are represented by the GADT {\em ComponentType}. There are
four forms of component type.
\begin{itemize}
\item
a mandatory named type component created by {\em MandatoryComponent};
\item
an optional named type component created by {\em OptionalComponent}. Note that once again we
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

Thus the components {\em aComponent} and {\em bComponent} used in table \ref{ASN1built-in} are
defined as
\begin{itemize}
\item
{\em MandatoryComponent (NamedType "a" (BuiltinType INTEGER))} and
\item
{\em MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN))} respectively.
\end{itemize}

ASN.1's set type is an unordered sequence.
The encoding of a set type value requires component tag information to order the components.
We provide the selector function {\em getCTI} to access tag information. It uses {\em getTI}
which is applied to an {\em ASNTYPE} which in turn uses {\em getBuiltinTI} which returns the
universal tag of a built-in ASN.1 type. The choice type requires a further function {\em
getCTags} to access the tags of a choice. The tag assigned to a untagged CHOICE type is the smallest
tag in the root of the CHOICE type. This may involve further nested untagged CHOICE types.
The function {\em getCTags} is also used in the encoding of a choice value.

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
getBuiltinTI (CHOICE c)         = (minimum . fst . snd . getCTags True ([],[])) c
getBuiltinTI (TAGGED t v)       = t

type ChoiceRootTags = [TagInfo]
type ChoiceExtTags = [TagInfo]
type InRoot = Bool

getCTags :: InRoot -> (ChoiceRootTags, ChoiceExtTags) -> Choice a -> (Bool, (ChoiceRootTags, ChoiceExtTags))
getCTags b tgs EmptyChoice                             = (b, tgs)
getCTags b tgs (ChoiceExtensionMarker xs)              = getCTags (not b) tgs xs
getCTags b tgs (ChoiceExtensionAdditionGroup vn xs)    = getCTags' b tgs xs
getCTags b (r,e) (ChoiceOption (NamedType n (BuiltinType (TAGGED t a))) xs)
     | b            = getCTags b (r ++ [t], e) xs
     | otherwise    = getCTags b (r, e ++ [t]) xs
getCTags b (r,e) (ChoiceOption (NamedType n a) xs)
     | b            = getCTags b (r ++ [getTI a], e) xs
     | otherwise    = getCTags b (r, e ++ [getTI a]) xs


getCTags' :: InRoot -> (ChoiceRootTags, ChoiceExtTags) -> Choice' a -> (Bool, (ChoiceRootTags, ChoiceExtTags))
getCTags' b tgs EmptyChoice'              = (b, tgs)
getCTags' b tgs ChoiceExtensionMarker'    = (b, tgs)
getCTags' b (r,e) (ChoiceOption' (NamedType n (BuiltinType (TAGGED t a))) xs)
     | b            = getCTags' b (r ++ [t], e) xs
     | otherwise    = getCTags' b (r, e ++ [t]) xs
getCTags' b (r,e) (ChoiceOption' (NamedType n a) xs)
     | b            = getCTags' b (r ++ [getTI a], e) xs
     | otherwise    = getCTags' b (r, e ++ [getTI a]) xs

\end{code}

\subsection{ASN.1 ChoiceType}
\label{choice}

The ASN.1 {\tt ChoiceType} has similarities to the {\tt SequenceType}. In effect it is a
sequence of optional components where exactly one must be used for any incarnation. We
therefore have chosen a Haskell representation which has significant similarities to our
representation of the {\tt SequenceType}.

We use a new GADT {\em Choice} which is presented below.

\begin{code}
data Choice a where
    EmptyChoice                     :: Choice Nil
    ChoiceExtensionMarker           :: Choice l -> Choice l
    ChoiceExtensionAdditionGroup    :: VersionNumber -> Choice' l -> Choice l
    ChoiceOption                    :: NamedType a -> Choice l -> Choice (a:*:l)

data Choice' a where
    EmptyChoice'                    :: Choice' Nil
    ChoiceOption'                   :: NamedType a -> Choice' l -> Choice' (a:*:l)
    ChoiceExtensionMarker'          :: Choice' Nil
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
but only one may ever be used for a particular incarnation. Note that unlike
a sequence an extension addition group may only be followed by an extension marker or nothing. The type
{\em Choice'} is used to represent the components of an extension addition group where {\em ChoiceExtensionMarker} indicates
the termination of the group followed by the terminating extension marker;
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
{\em AddAValue} which adds a value to a list. It can only be applied to a list for which no
choice has yet been made indicated by the type of the input list.
Its return type is {\em ExactlyOne (a:*:l) SelectionMade)} indicating a choice has now been made.
{\em SelectionMade} is also a type with no associated values; and
\item
{\em AddNoValue} which adds no value (of the appropriate type -- hence the use
of the phantom type {\em NoValue a}) to a list. In this case the number of values in the
list is not incremented. That is, if the input list indicates that no selection has yet been
made with {\em NoSelectionMade}, then so will the output list.
\end{itemize}

A phantom type is one in which a type variable appears only on the left hand side of the
type's definition. Thus a value of the type -- such as {\em NoValue} -- can match many
different types. We use this as a placeholder for the non-selected components of a choice
type which will need to satisfy the various component types.

It is important to have the constructors {\em AddAValue} and {\em AddNoValue} so that there is
a match between the choice value and the choice type.
That is, the overall choice value has the
appropriate type, and the particular choice of value has the required type.

In common with the heterogeneous list type, we have added {\em ExactlyOne} to the type classes
{\em Show} and {\em Eq}.

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

The type {\em Enumerate} represents an enumeration built from {\em EnumerationItem}s. This
has three constructors:
\begin{itemize}
\item
{\em EmptyEnumeration} which represents an empty enumeration;
\item
{\em AddEnumeration} which adds an {\em EnumerationItem} to an existing enumeration; and
\item
{\em EnumerationExtensionMarker} which indicates the existence of an extension marker.
\end{itemize}

\begin{code}

data EnumerationItem = Identifier Name
                       | NamedNumber Name Integer
								 deriving (Show, Eq) 

data Enumerate = EmptyEnumeration
                 | AddEnumeration EnumerationItem Enumerate
                 | EnumerationExtensionMarker Enumerate
								 deriving (Show, Eq)

\end{code}

The function {\em assignIndex} which assigns an index to each enumeration item is defined here
since it is used in the {\tt PER} and {\tt ConstraintGeneration} modules when encoding an 
enumeration value and generating an enumeration constraint respectively. It returns a pair
whose first element indicates if an extension marker is present in the type, and whose second
element is a list of indices assigned to the enumeration values. The index assigned to each
enumeration value is determined by the enumeration number associated with each enumeration.
These are either assigned explicitly when the enumeration is defined, or implicitly by the
function {\em assignNumber}.

\begin{code}

assignIndex :: Enumerate -> (Bool, [Integer])
assignIndex en
    = let (b,ns) = assignNumber en False []
          sls = sort ns
      in
        (b, positions ns sls)

assignNumber :: Enumerate -> Bool -> [Integer] -> (Bool, [Integer])
assignNumber en b ls
    = let nn = getNamedNumbers en
      in
        assignN ([0..] \\ nn) en b ls

assignN :: [Integer] -> Enumerate -> Bool -> [Integer] -> (Bool, [Integer])
assignN (f:xs) EmptyEnumeration b ls = (b,reverse ls)
assignN (f:xs) (AddEnumeration  (NamedNumber _ i) r)b ls = assignN (f:xs) r b (i:ls)
assignN (f:xs) (AddEnumeration  _ r) b ls = assignN xs r b (f:ls)
assignN (f:xs) (EnumerationExtensionMarker   r) b ls = (True, reverse ls)
assignN [] _ _ _ = error "No numbers to assign"

getNamedNumbers :: Enumerate -> [Integer]
getNamedNumbers EmptyEnumeration = []
getNamedNumbers (AddEnumeration  (NamedNumber _ i) r) = i:getNamedNumbers r
getNamedNumbers (AddEnumeration  _ r) = getNamedNumbers r
getNamedNumbers (EnumerationExtensionMarker   r)  = []

noEnums :: Enumerate -> Integer
noEnums EmptyEnumeration = 0
noEnums (AddEnumeration  _ r) = 1 + noEnums r
noEnums (EnumerationExtensionMarker   r)  = 0

positions [] sls = []
positions (f:r) sls
    = findN f sls : positions r sls

findN i (f:r)
    = if i == f then 0
        else 1 + findN i r
findN i []
    = error "Impossible case!"
\end{code}
