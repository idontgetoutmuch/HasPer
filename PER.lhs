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

In this paper we will present ASN.1 types and values using {\tt teletext} font and Haskell
code and expressions using {\em italic} font. The paper includes the actual Haskell
implementation of PER. Any code segments are separated from the main text of the paper by a
newline.

%include ASNTYPE.lhs

In the following section we describe the Packed Encoding Rules (PER) as described in X.691.
These are defined in the module {\em PER}.
There are two versions of these rules, BASIC-PER and CANONICAL-PER. They both have two
variants, UNALIGNED and ALIGNED. The later variant may require some bit padding to restore
octet alignment. We have implemented the UNALIGNED variant of CANONICAL-PER.

\section{UNALIGNED CANONICAL-PER}

%if False

\begin{code}

{-# OPTIONS_GHC -XMultiParamTypeClasses -XGADTs -XTypeOperators
                -XEmptyDataDecls -XFlexibleInstances -XFlexibleContexts
                -fwarn-unused-binds
#-}
{-
                -fwarn-unused-imports -fwarn-incomplete-patterns
-}

\end{code}

%endif

The module uses the following modules:
\begin{itemize}
\item
{\em ASNTYPE} since the encoding functions require ASN.1 type;
\item
{\em LatticeMod} in which some type classes are defined, including the type class {\tt
Lattice}, which specifies a {\bf bounded lattice} and those types which have bounded lattice
characteristics. This enables the overloading of various bounded lattice-related entities such as
{\em top} and {\em bottom}. This module is described in section \ref{lattice};
\item
{\em ConstraintGeneration} in which the constraint processing functions are defined. This is
required since the top-level encoding functions take a list of constraints as input -- the
serially applied constraints -- and require two constraints to represent the effective
constraint (which is used in the generation of an encoding) and the actual constraint (which
is used for validity testing). This module is described in section \ref{constraintGen};
\item
{\em ASN1.PER.Integer} in which the functions {\em fromNonNegativeBinaryInteger'} and {\em
from2sComplement'} are defined. These are used in the decoding of integers. Note that in Haskell
the totality of a module is imported unless explicitly specified within parentheses; and
\item
several Haskell library modules some of which have been qualified with a shorter name which is then used
as a prefix when any entity of these modules is used.
\end{itemize}

\begin{code}

module PER where

import ASNTYPE
import LatticeMod
import ConstraintGeneration
import Language.ASN1.PER.Integer
   ( fromNonNegativeBinaryInteger'
   , toNonNegativeBinaryInteger
   , from2sComplement'
   , to2sComplement
   )
import Data.List hiding (groupBy)
import Data.Char
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Writer

import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.BitPut as BP
import Data.Int
import Data.Maybe

\end{code}



The top-level PER encoding function is called {\em encode}. The function takes three inputs:
the type of value being encoded; a list of subtype constraints which represents the
serially applied constraints and will be converted into an effective constraint
in advance of encoding; and the value to be encoded.
It has three distinct
cases which address the various forms of an ASNType.
\begin{itemize}
\item
The input is a builtin type value. The function {\em toPer} is called on this value.
\item
The input is a referenced type value. The reference is dropped
and {\em encode} is recursively called on the value.
\item
The input is a constrained type value. The constraint is added to the list of constraints and
the function is called again on the type being constrained. This recursion will continue
until we reach a non-constrained type. The associated list of constraints will then include all
of the seraily applied constraints.
\end{itemize}

The function {\em encode} returns a value of type {\em PERMonad ()}. This is a writer monad
wrapped up inside an error monad thus enabling the writing of the bits that represent the
encoding as a {\em BitStream} value, and the reporting of any errors incurred during encoding.
The error type {\em ASNError} enables the categorisation of the various types of error.


\begin{code}
type PERMonad a = ErrorT ASNError (WriterT BitStream Identity) a

data ASNError =
     ConstraintError String
   | BoundsError     String
   | DecodeError     String
   | ExtensionError  String
   | OtherError      String
      deriving Show

instance Error ASNError where
   noMsg = OtherError "The impossible happened"


type PerEncoding = Either String BitStream


encode :: ASNType a -> SerialSubtypeConstraints a -> a -> PERMonad ()
encode (BuiltinType t) cl v       = toPER t v cl
encode (ReferencedType r t) cl v  = encode t cl v
encode (ConstrainedType t c) cl v = encode t (c:cl) v

encode' :: ASNType a -> SerialSubtypeConstraints a -> a -> AMonad ()
encode' (BuiltinType t) cl v       = toPER' t v cl
encode' (ReferencedType r t) cl v  = encode' t cl v
encode' (ConstrainedType t c) cl v = encode' t (c:cl) v

\end{code}

The function {\em toPER} takes an {\em ASNBuiltin} type, a value of the same builtin type and
a list of subtype constraints, and encodes the value using PER. The first input is essential
in determining the encoding algorithm to use. That is, it is a pointer to the appropriate
encoding function for the value. For example, if the type is {\em INTEGER} then {\em
encodeInt} is called, and if it is a {\em CHOICE} type then {\em encodeChoice} is used.

\begin{code}

toPER :: ASNBuiltin a -> a -> SerialSubtypeConstraints a -> PERMonad ()
toPER NULL _ _             = tell []
toPER INTEGER x cl         = encodeInt cl x
toPER VISIBLESTRING x cl   = encodeRCS cl x
toPER PRINTABLESTRING x cl = encodeRCS cl x
toPER NUMERICSTRING x cl   = encodeRCS cl x
toPER IA5STRING x cl       = encodeRCS cl x
toPER BMPSTRING x cl       = encodeRCS cl x
toPER UNIVERSALSTRING x cl = encodeRCS cl x
toPER BOOLEAN x cl         = encodeBool cl x
toPER (ENUMERATED e) x cl  = encodeEnum e x -- no PER-Visible constraints
toPER (BITSTRING nbs) x cl = encodeBitstring nbs cl x
toPER (OCTETSTRING) x cl   = encodeOctetstring cl x
toPER (SEQUENCE s) x cl    = encodeSequence s x -- no PER-Visible constraints
toPER (SEQUENCEOF s) x cl  = encodeSeqOf cl s x
toPER (SET s) x cl         = encodeSet s x -- no PER-Visible constraints
toPER (CHOICE c) x cl      = encodeChoice c x -- no PER-visible constraints
toPER (SETOF s) x cl       = encodeSeqOf cl s x -- no PER-visible constraints
toPER (TAGGED tag t) x cl  = encode t cl x

toPER' :: ASNBuiltin a -> a -> SerialSubtypeConstraints a -> AMonad ()
toPER' (BITSTRING nbs) x cl = encodeBitString nbs cl x

\end{code}

\section{COMPLETE ENCODING}
{- FIXME: Need a more efficient way to do this. Could carry the remainder with each encoding?
-}
{- X691REF: 10.1 -}

{\em extractValue} is simply a function that extracts the encoding bits from the monadic value
returned by the encoding functions.

\begin{code}

extractValue  = runIdentity . runWriterT . runErrorT

completeEncode :: PERMonad () -> PERMonad ()
completeEncode m
    = let v = snd . extractValue $ m
      in tell (padding v)

padding enc
    = let le  = length enc
          bts = le `mod` 8
          pad = if le == 0
                        then [0,0,0,0,0,0,0,0]
                        else if bts == 0
                                then enc
                                else enc ++ take (8-bts) [0,0..]
          in pad

\end{code}

\section{ENCODING AN OPEN TYPE FIELD}



{\em encodeOpen} encodes an open type value.

\begin{code}

encodeOpen :: ASNType a -> a -> PERMonad ()
encodeOpen t v
{- X691REF: 10.2.1 -}   = let (_,enc) = extractValue (completeEncode (encode t [] v))
{- X691REF: 10.2.2 -}     in  encodeOctetsWithLength enc

\end{code}

\section{ENCODING A LENGTH DETERMINANT}

Several PER encodings require the encoding of a length determinant. If the item to be encoded
is very large or, in the case of integer encoding, the number of bits produced by the encoding
is very large, then some fragmenting may be required in which length and value encodings are
interleaved.

{\em encodeWithLength} is a higher order function which takes a constraint, an encoding function and a list of
values (could be bits, octets or any ASN.1 type). The approach to encoding depends on whether
the constraint imposes an upper bound which is less than 64K. If it does then no interleaving is required and
the value is encoded with a length prefix if the upper bound differs from the lower bound, and
with no length encoding otherwise.

If the upper bound is at least 64K then {\em encodeUnconstrainedLength} is called. The items are grouped first in 16k batches, and then
in batches of 4. The input encoding function is then supplied as
an input to the function {\em encodeUnconstrainedLength} which manages the interleaving of
length and value encodings -- it encodes the length and values of
each batch and concatenates their resulting bitstreams together.
Note the values are encoded using the input function.

Note that {\em encodeWithLength} is not used to encode {\bf normally small length}
determinants (see X691: 10.9.3.4} which are only used with the bitmap that prefixes the
extension addition values of a set or sequence type.

\begin{code}

encodeWithLength :: IntegerConstraint -> (t -> PERMonad ()) -> [t] -> PERMonad ()
encodeWithLength ic fun ls
    = if constrained ic && ub < k64
          then {- X691REF: 10.9.4.1 -}
                if lb == ub
                    then
                         do tell []
                            mapM_ fun ls
                    else
                        do encodeConstrainedInt (fromInteger (genericLength ls) - lb, ub-lb)
                           mapM_ fun ls
          else {- X691REF: 10.9.4.2 -}
               encodeUnconstrainedLength fun ls
      where
       lb = lower ic
       ub = upper ic

k64 :: InfInteger
k64 = 64 * 2^10
\end{code}

{\em encodeUnconstrainedLength} is a higher order function which encodes a value with an
unconstrained length i.e. it either has no upper bound on the size of the value,
or the upper bound is at least 64k. The inputs are the value encoding
function and the list of values to be encoded. If the length of the input value is less than
16K then the length is encoded followed by the value. Otherwise the auxiliary function {\em
encodeUnconstrainedLengthAux} is called. This function manages the fragmenting of the input
value into blocks of at most four 16K blocks. These are each encoded -- their block length
followed by the encoding of the block of values -- and if the block contains four 16k
blocks the process is repeated with the next block of 16K values.

{\em lengthLessThan16K} encodes the length of a list of less than 16K values and {\em blockLen}
encodes the length of a block (1 to 4).

\begin{code}

encodeUnconstrainedLength :: (b -> PERMonad ()) -> [b] -> PERMonad ()
encodeUnconstrainedLength encFun [] = lengthLessThan16K 0 {- FIXME: Is this only the case when there is at least 16k values? 10.9.3.8.3 -}
encodeUnconstrainedLength encFun xs
    | l < k16
    {- X691REF: 10.9.3.6 AND 10.9.3.7 -}
        = do lengthLessThan16K l
             mapM_ encFun xs
    | otherwise
    {- X691REF: 10.9.3.8 -}
       = encodeUnconstrainedLengthAux encFun xs
         where l = genericLength xs

encodeUnconstrainedLengthAux :: (b -> PERMonad ()) -> [b] -> PERMonad ()
encodeUnconstrainedLengthAux encFun [] = throwError (OtherError "Nothing to encode")
encodeUnconstrainedLengthAux encFun xs
    | l == 4 && last16 == k16
        = do blockLen 4 63
             mapM_ (mapM_ encFun) x
             encodeUnconstrainedLength encFun (drop (64*(2^10)) xs)
    | otherwise
        = if last16 == k16
             then do blockLen l 63
                     mapM_ (mapM_ encFun) x
                     lengthLessThan16K 0
             else do blockLen (l-1) 63
                     mapM_ (mapM_ encFun) (init x)
                     lengthLessThan16K ((genericLength.last) x)
                     mapM_ encFun (last x)
    where
        (x:_)      = (groupBy 4 . groupBy (16*(2^10))) $ xs
        l          = genericLength x
        last16     = (genericLength . last) x

k16 :: InfInteger
k16    = 16*(2^10)

groupBy :: Int -> [t] -> [[t]]
groupBy n =
   unfoldr k
      where
         k [] = Nothing
         k p = Just (splitAt n p)

lengthLessThan16K :: InfInteger -> PERMonad ()
lengthLessThan16K n
   | n <= 127
     {- X691REF: 10.9.3.6 -}
        = do tell [0]
             encodeConstrainedInt (n, 127)
   | n < k16
     {- X691REF: 10.9.3.7 -}
        = do tell [1]
             tell [0]
             encodeConstrainedInt (n, (k16-1))
   | otherwise
        = throwError (BoundsError "Length is out of range.")

blockLen :: InfInteger -> InfInteger -> PERMonad ()
blockLen x y
    = do tell [1]
         tell [1]
         encodeConstrainedInt (x,y)

\end{code}


\section{ENCODING THE BOOLEAN TYPE}

\begin{code}

{- FIXME: I think this is as good as it's worth doing for now -}
{- Clearly we want to just say e.g. tell 1                    -}
{- Or do we. It is meant to return a bit-field value and not just a bit -}
{- So the following whould be fine. -}
encodeBool :: [SubtypeConstraint Bool] -> Bool -> PERMonad ()
encodeBool t True = tell [1]
encodeBool t _    = tell [0]

\end{code}

\section{ENCODING THE INTEGER TYPE}
\label{intEnc}

If the type is unconstrained -- as indicated by an empty constraint list --  then the value is
encoded as an unconstrained integer using the function {\em encodeUnconsInt}. If the type has
a constraint then the function {\em encodeIntWithConstraint} is called. The encoding depends on
whether the constraint is extensible and whether the value lies within the extenstion root.

Note that the third input to {\em encodeIntWithConstraint} is the last of the serially applied
constraints. This is because if a constraint is serially applied to an extensible constraint
then any extension additions of the extensible constraint are discarded (see X.680 Annex
G.4.2.3). That is, the extensibility and extension additions of the effective constraint are
determined only by the last constraint.

\begin{code}

encodeInt :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
encodeInt [] v = {- X691REF: 12.2.4 -} encodeUnconsInt v
encodeInt cs v = encodeIntWithConstraint cs v

\end{code}


{\em encodeUnconsInt} encodes an integer value as a 2's-complement-binary-integer
into a minimum number of octects using {\em to2sComplement}. This is prefixed by an explicit
length encoding using {\em encodeOctetsWithLength}.

\begin{code}

encodeUnconsInt :: InfInteger -> PERMonad ()
encodeUnconsInt (Val x) = encodeOctetsWithLength . to2sComplement $ x
encodeUnconsInt v  = throwError (BoundsError ("Cannot encode " ++ show v))

\end{code}


{\em encodeIntWithConstraint} calls:
\begin{itemize}
\item
{\em encodeNonExtConsInt} if the constraint is not extensible. This takes three inputs: the
actual constraint which is used to test whether the value to be encoded is valid, the
effective constraint which is used to encode the value, and the value to be encoded.
The constraints are generated by functions defined in the module {\em ConstraintGeneration};
\item
{\em encodeExtConsInt} if the constraint is extensible. This function takes five
inputs. The three required for {\em encodeNonExtConsInt} and the two -- actual and effective
-- extension constraints.
\end{itemize}

\begin{code}

encodeIntWithConstraint :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
encodeIntWithConstraint cs v
    = if (not extensible)
        then {- X691REF: 12.2 -} encodeNonExtConsInt validCon effCon v
        else {- X691REF: 12.1 -} encodeExtConsInt validCon effCon v
      where
          effCon :: Either String (ExtBS (ConType IntegerConstraint))
          effCon = lSerialEffCons integerConElements top cs
          validCon :: Either String (ExtBS (ConType ValidIntegerConstraint))
          validCon = lSerialEffCons integerConElements top cs
          extensible = eitherExtensible effCon

eitherExtensible (Right v) = isExtensible v
eitherExtensible _ = False

\end{code}



{\em encodeNonExtConsInt} has to deal with five cases.
\begin{itemize}
\item
The constraint is empty and thus no values can be encoded. An appropriate error is thrown.
\item
The constraint does not restrict the integer to be either constrained or semi-constrained. The
value is encoded as an unconstrained integer using {\em encodeUnconsInt}.
\item
The constraint restricts the integer to be a semi-constrained integer and the value satisfies
the constraint. The value is encoded
using {\em encodeSemiConsInt}.
\item
The constraint restricts the integer to be a constrained integer and the value satisfies the
constraint. The value is encoded using
{\em encodeConstrainedInt}.
\item
The value does not satisfy the constraint. An appropriate error is thrown.
\end{itemize}

\begin{code}
encodeNonExtConsInt :: Either String (ExtBS (ConType ValidIntegerConstraint))
                     -> Either String (ExtBS (ConType IntegerConstraint))
                     -> InfInteger
                     -> PERMonad ()
encodeNonExtConsInt (Right validCon) (Right effCon) n
    | isEmptyConstraint effRootCon
         = throwError (ConstraintError "Empty constraint")
    | isNonEmptyConstraint effRootCon && inRange n validRootCon
         = case constraintType effRootCon of
                 UnConstrained
                        -> {- X691REF: 12.2.4 -}
                            encodeUnconsInt n
                 SemiConstrained
                        -> {- X691REF: 12.2.3 -}
                            encodeSemiConsInt n rootLower
                 Constrained
                        -> {- X691REF: 12.2.2 -}
                            encodeConstrainedInt ((n - rootLower), rootUpper - rootLower)
    | otherwise
        = throwError (BoundsError "Value out of range")
          where
            effRootCon   = conType $ getRC effCon
            validRootCon = conType $ getRC validCon
            rootLower    = lower effRootCon
            rootUpper    = upper effRootCon
encodeNonExtConsInt _ _ _ = throwError (ConstraintError "Invalid constraint")

\end{code}


The functions {\em isNonEmptyConstraint} and {\em isEmptyConstraint} test whether the
combination of PER-visible constraints results in an actual
constraint or no constraint. For example, the intersection of two mutually exclusive
constraints results in no constraint. This will then mean that their can be no valid values
and an error must be reported.

The function {\em inRange} tests with a value satisfies a constraint. It is tested
against the actual constraint and not against the effective constraint which is used for
encoding.

\begin{code}

isNonEmptyConstraint,isEmptyConstraint :: (Eq t, Lattice t) => t -> Bool
isNonEmptyConstraint x  = x /= bottom
isEmptyConstraint       = (not . isNonEmptyConstraint)

inRange :: InfInteger -> ValidIntegerConstraint -> Bool
inRange _ (Valid [])       = False
inRange n (Valid (x:rs))   = n >= (lower x) && n <= (upper x) || inRange n (Valid rs)

\end{code}

{\em encodeExtConsInt} is similar to {\em encodeNonExtConsInt}. It has the five cases
described for {\em encodeNonExtConsInt} -- where any encoding is prefixed by the bit 0 --
plus the case when the value satisfies the constraint
but is not within the extension root. In this case the value is encoded as an unconstrained
integer using {\em encodeUnconsInt} prefixed by the bit 1.

\begin{code}

encodeExtConsInt :: Either String (ExtBS (ConType ValidIntegerConstraint))
                     -> Either String (ExtBS (ConType IntegerConstraint))
                     -> InfInteger
                     -> PERMonad ()
encodeExtConsInt (Right validCon) (Right effCon)  n
             | isEmptyConstraint effRootCon && isEmptyConstraint effExtCon
                  = throwError (ConstraintError "Empty constraint")
             | isNonEmptyConstraint effRootCon && inRange n validRootCon
                  = case constraintType effRootCon of
                            UnConstrained -> {- X691REF: 12.1 and 12.2.4 -}
                                 do tell [0]
                                    encodeUnconsInt n
                            SemiConstrained -> {- X691REF: 12.1 and 12.2.3 -}
                                 do tell [0]
                                    encodeSemiConsInt n rootLower
                            Constrained -> {- X691REF: 12.1 and 12.2.4 -}
                                 do tell [0]
                                    encodeConstrainedInt ((n - rootLower), (rootUpper - rootLower))
             | isNonEmptyConstraint effExtCon && inRange n validExtCon
                  = do  {- X691REF: 12.1 -}
                        tell [1]
                        encodeUnconsInt n
             | otherwise
                  = throwError (BoundsError "Value out of range")
                    where
                        effRootCon = conType $ getRC effCon
                        validRootCon = conType $ getRC validCon
                        effExtCon = conType $ getEC effCon
                        validExtCon = conType $ getEC validCon
                        rootLower          = lower effRootCon
                        rootUpper          = upper effRootCon


\end{code}

{\em encodeSemiConsInt} encodes a semi-constrained integer. The difference between the value and the
lower bound is encoded as a non-negative-binary-integer in the mininum number of octets using
{\em encodeNonNegBinaryIntInOctets}. This is prefixed by an encoding of the length of the
octets using {\em encodeOctetsWithLength}.

\begin{code}

encodeSemiConsInt :: InfInteger -> InfInteger -> PERMonad ()
encodeSemiConsInt x@(Val v) y@(Val lb)
    = encodeOctetsWithLength (encodeNonNegBinaryIntInOctets (x-y))
encodeSemiConsInt n (Val lb)
    = throwError (BoundsError ("Cannot encode " ++ show n ++ "."))
encodeSemiConsInt _ _
    = throwError (ConstraintError "No lower bound.")


encodeNonNegBinaryIntInOctets :: InfInteger -> BitStream
encodeNonNegBinaryIntInOctets (Val x) =
   (reverse . (map fromInteger) . flip (curry (unfoldr (uncurry g))) 8) x where
      g 0 0 = Nothing
      g 0 p = Just (0,(0,p-1))
      g n 0 = Just (n `mod` 2,(n `div` 2,7))
      g n p = Just (n `mod` 2,(n `div` 2,p-1))

\end{code}

{\em encodeOctetsWithLength} encodes a collection of octets with
unconstrained length. {\em encodeBitsWithLength} does the same except
for a collection of bits.

\begin{code}

encodeOctetsWithLength :: [Int] -> PERMonad ()
encodeOctetsWithLength = encodeUnconstrainedLength tell . groupBy 8


encodeBitsWithLength :: [Int] -> PERMonad ()
encodeBitsWithLength = encodeUnconstrainedLength (tell . return)

\end{code}


{\em encodeConstrainedInt} encodes an integer in the minimum
number of bits required for the range specified by the constraint
(assuming the range is at least 2). The value encoded is the offset from the lower bound of
the constraint.


\begin{code}

encodeConstrainedInt :: (InfInteger, InfInteger) -> PERMonad ()
encodeConstrainedInt (Val val, Val range)
    = tell $ (reverse . (map fromInteger) . unfoldr encodeConstrainedIntAux) (val,range)

encodeConstrainedIntAux (_,0) = Nothing
encodeConstrainedIntAux (0,w) = Just (0, (0, w `div` 2))
encodeConstrainedIntAux (n,w) = Just (fromIntegral (n `mod` 2), (n `div` 2, w `div` 2))

\end{code}


\section{ENCODING THE ENUMERATED TYPE}

{\em encodeEnum} takes the defined enumeration type and the enumeration value and
first applies the function {\em assignIndex} to the enumeration type. This returns a pair
whose first element indicates if an extension marker is present in the type, and whose second
element is a list of indices assigned to the enumeration values. The index assigned to each
enumeration value is determined by the enumeration number associated with each enumeration.
These are either assigned explicitly when the enumeration is defined, or implicitly by the
function {\em assignNumber}.

{\em encodeEnum} calls the auxiliary function {\em encodeEnumAux} which manages the various
encoding cases. Its second input is the number of enumeration root values which is required
since a root enumeration will be encoded as a constrained integer.

Note that {\em encodeEnum} does not have a constraint input since there are no PER-visible
enumerated type constraints.

\begin{code}

encodeEnum :: Enumerate a -> ExactlyOne a SelectionMade -> PERMonad ()
encodeEnum e x
    = let (extensible,inds) = assignIndex e {- X691REF: 13.1 -}
          no = genericLength inds
      in
        encodeEnumAux extensible no inds e x


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
assignN (f:xs) EmptyEnumeration b ls = (b,reverse ls)
assignN (f:xs) (AddEnumeration  (NamedNumber _ i) r)b ls = assignN (f:xs) r b (i:ls)
assignN (f:xs) (AddEnumeration  _ r) b ls = assignN xs r b (f:ls)
assignN (f:xs) (EnumerationExtensionMarker   r) b ls = (True, reverse ls)
assignN [] _ _ _ = error "No numbers to assign"

getNamedNumbers :: Enumerate a -> [Integer]
getNamedNumbers EmptyEnumeration = []
getNamedNumbers (AddEnumeration  (NamedNumber _ i) r) = i:getNamedNumbers r
getNamedNumbers (AddEnumeration  _ r) = getNamedNumbers r
getNamedNumbers (EnumerationExtensionMarker   r)  = []

noEnums :: Enumerate a -> Integer
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

{\em encodeEnumAux} is a recursive function which recurses through the enumeration value until
it reaches the enumeration. If no extension marker is present then the enumeration is
encoded using {\em encodeConstrainedInt}. If the marker is present and the enumeration is
in the extension root then it is encoded as above but prefixed by 0.

If the enumeration is not in the extension root then the encoding is passed to a second
auxiliary function {\em encodeEnumExtAux}. This is also a recursive function which encodes an
enumeration as a normally small non-negative integer using {\em encodeNSNNInt} prefixed by a
1.

\begin{code}

encodeEnumAux :: Bool -> Integer -> [Integer] -> Enumerate a -> ExactlyOne a n
                 -> PERMonad ()
encodeEnumAux extensible no (f:r) (AddEnumeration  _ es) (AddAValue a rest)
    = if not extensible
        then    {- X691REF: 13.2 -}
                encodeConstrainedInt (fromInteger f, fromInteger (no-1))
        else do {- X691REF: 13.2 -}
                tell [0]
                encodeConstrainedInt (fromInteger f, fromInteger (no-1))
encodeEnumAux b no (f:r) (AddEnumeration  _ es) (AddNoValue a rest)
    = encodeEnumAux b no r es rest
encodeEnumAux b no inds (EnumerationExtensionMarker   ex) x
    = let el = noEnums ex
      in encodeEnumExtAux 0 el ex x
encodeEnumAux _ _ _ _ _ = throwError (OtherError "No enumerated value!")

encodeEnumExtAux :: Integer -> Integer -> Enumerate a -> ExactlyOne a n
                    -> PERMonad ()
encodeEnumExtAux i l (AddEnumeration  _ es) (AddAValue a rest)
    = do    {- X691REF: 13.3 -}
            tell [1]
            encodeNSNNInt i 0
encodeEnumExtAux i l (AddEnumeration  _ es) (AddNoValue a rest)
    = encodeEnumExtAux (i+1) l es rest
encodeEnumExtAux i l _ _ = throwError (OtherError "No enumerated extension value!")

\end{code}

{\em encodeNSNNInt} encodes a normally small non-negative integer.
\begin{code}

encodeNSNNInt :: Integer -> Integer -> PERMonad ()
encodeNSNNInt n lb
    = if n <= 63
        then do {- X691REF: 10.6.1 -}
                tell [0]
                encodeConstrainedInt (fromInteger n, fromInteger 63)
        else do {- X691REF: 10.6.2 -}
                tell [1]
                encodeSemiConsInt (fromInteger n) (fromInteger lb)


\end{code}

\section{ENCODING THE REAL TYPE} {- FIXME: To do? -}

\section{ENCODING THE BIT STRING TYPE}


{\em encodeBitstring} takes the usual two inputs -- the list of serially applied constraints
and the value to be encoded -- and an additional input, the named bits of type {\em
NamedBits}. If the constraint list is empty the function {\em encodeUnconstrainedBitstring} is
called. Otherwise, {\em encodeBitstringWithConstraint} is called. Note that there are two ways
in which a BITSTRING type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible. This is determined when generating the effective constraint
for a type using the function {\em lSerialEffCon} defined in the module {\em
ConstraintGeneration}.

\begin{code}

encodeBitstring :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PERMonad ()
encodeBitstring nbs [] x
    = {- X691REF: 15.2 -}
      encodeUnconstrainedBitstring nbs x
encodeBitstring nbs cs x
    = {- X691REF: 15.3 -}
      encodeBitstringWithConstraint nbs cs x

\end{code}

{\em encodeUnconstrainedBitstring} encodes the bitstring with a length determinant using {\em
encodeBitsWithLength}. If there are any named bits then trailing 0 bits are removed in advance
of encoding.

\begin{code}
encodeUnconstrainedBitstring :: NamedBits -> BitString -> PERMonad ()
encodeUnconstrainedBitstring namedBits (BitString [])
    = tell []
encodeUnconstrainedBitstring namedBits (BitString bs)
    = let rem0 = if (not.null) namedBits
                    then {- X691REF: 15.2 -}
                            strip0s bs
                    else bs
      in {- X691REF: 15.11 with ub unset -}
            encodeBitsWithLength rem0


strip0s :: BitStream -> BitStream
strip0s [] = []
strip0s bs
    = if last bs == 0
        then strip0s (init bs)
        else bs

\end{code}

{\em encodeBitstringWithConstraint} calls {\em encodeNonExtConsBitstring} if the constraint is not
extensible. If it is extensible then {\em encodeExtConsBitstring} is called. They both take the
effective constraint and actual constraint associated with the type as input.

\begin{code}

encodeBitstringWithConstraint :: NamedBits -> [SubtypeConstraint BitString] -> BitString
                                 -> PERMonad ()
encodeBitstringWithConstraint namedBits cs v
    = if (not extensible)
        then {- X691REF: 15.7 -}
             encodeNonExtConsBitstring namedBits validCon effCon v
        else {- X691REF: 15.6 -}
             encodeExtConsBitstring namedBits validCon effCon v
      where
          effCon :: Either String (ExtBS (ConType IntegerConstraint))
          effCon = lSerialEffCons lBSConE top cs
          validCon :: Either String (ExtBS (ConType ValidIntegerConstraint))
          validCon = lSerialEffCons lBSConE top cs
          extensible = eitherExtensible effCon

\end{code}

{\em encodeNonExtConsBitstring} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedBitstring} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedBitstring} is called.
\end{itemize}

\begin{code}

encodeNonExtConsBitstring :: NamedBits -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> Either String (ExtBS (ConType IntegerConstraint))
                -> BitString
                -> PERMonad ()
encodeNonExtConsBitstring nbs _ (Right (ExtBS (ConType (IntegerConstraint NegInf PosInf)) _ _))
            (BitString vs)
    =   {- X691REF: 15.11 with ub unset -}
        encodeUnconstrainedBitstring nbs (BitString vs)
encodeNonExtConsBitstring nbs (Right ok) (Right vsc) (BitString vs)
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = {- X691REF: 15.8 - 15.11 -}
             encodeConstrainedBitstring [] nbs l u vrc vs
             where
                rc = conType . getRC $ vsc
                l = lower rc
                u = upper rc
                vrc = conType . getRC $ ok

\end{code}

{\em encodeExtConsBitstring} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedBitstring} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedBitstring} is called with the prefix bit
set to 0. If this results in an error (the value cannot satisfy the constraint root) then {\em
encodeNonExtRootBitstring} is called. The Haskell library function {\em catchError}
manages the error/non-error cases.
\end{itemize}


\begin{code}

encodeExtConsBitstring :: NamedBits -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> Either String (ExtBS (ConType IntegerConstraint))
                -> BitString
                -> PERMonad()
encodeExtConsBitstring nbs _
    (Right (ExtBS (ConType (IntegerConstraint NegInf PosInf))
                  (ConType (IntegerConstraint NegInf PosInf)) _)) (BitString vs)
    =   {- X691REF: 15.11 with ub unset -}
        encodeUnconstrainedBitstring nbs (BitString vs)
encodeExtConsBitstring nbs (Right ok) (Right vsc) (BitString vs)
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = do
                catchError ({- X691REF: 15.6 within root -}
                            encodeConstrainedBitstring [0] nbs l u vrc vs)
                           (\err -> do {- X691REF: 15.6 not in root -}
                                       encodeNonExtRootBitstring nbs rc ec vec vs)
             where
                rc = conType . getRC $ vsc
                l = lower rc
                u = upper rc
                ec = conType . getEC $ vsc
                vrc = conType . getRC $ ok
                vec = conType . getEC $ ok

\end{code}

{\em
{\em encodeConstrainedBitstring} takes a prefix bit as the first
input and has two list-pattern based cases. The first case has an empty list
as its second argument indicating that there are no named bits. The second case uses the
pattern {\em (b:rs)} to indicate that there is at least one named bit.

Note that X.691 15.8 states that if a bitstring is constrained to be of zero length then
it shall not be encoded. It is not clear whether this means that a bitstring with no length is
not encoded, or if any bitstring associated with a bitstring type with a zero-length
constraint is not encoded. We have implemented it using the former case. That is, the
bitstring must satisfy the constraint (up to the removal of trailing 0 bits as described in
X.691 15.3).
\begin{code}

type PrefixBit = BitStream

encodeConstrainedBitstring :: PrefixBit -> NamedBits -> InfInteger -> InfInteger
                                -> ValidIntegerConstraint -> BitStream -> PERMonad ()
encodeConstrainedBitstring pb [] l u (Valid vrc) xs
   | inSizeRange xs vrc
            = encodeConBS pb l u xs
   | otherwise
            = throwError (BoundsError "Size out of range")
encodeConstrainedBitstring pb (b:rs) l u _ xs
    = {- X691REF: 15.3 -}
       do
         (v,bs) <- return $ extractValue $ namedBitsEdit l u xs
         encodeC (encodeConBS pb l u) (v,bs)

encodeC fun (Left x,bs)  = throwError (BoundsError "Invalid length")
encodeC fun (_,bs)   = fun bs
\end{code}

{\em inSizeRange} is a predicate that tests whether a value satisfies a size constraint. The
length of the value is tested against the actual constraint -- possibly a non-contiguous set
of values -- and not against the effective constraint.

{\em namedBitsEdit} applies the necessary pruning of or appending of 0s to a bitstring to
produce a minimal size value that satisfies the constraint associated with the type. This is
only applied when the BIT STRING type has associated named bits.

\begin{code}

inSizeRange :: [b] -> [IntegerConstraint] -> Bool
inSizeRange _  [] = False
inSizeRange p qs = inSizeRangeAux qs
   where
      l = genericLength p
      inSizeRangeAux (x:rs) =
         l >= (lower x) && l <= (upper x) || inSizeRangeAux rs
      inSizeRangeAux [] = False


namedBitsEdit :: InfInteger -> InfInteger -> BitStream -> PERMonad ()
namedBitsEdit l u xs
    = let lxs = genericLength xs
      in if lxs < l
        then add0s (l-lxs) xs
        else
            if lxs > u
             then rem0s (lxs-u) l xs
             else rem0s' l xs

add0s :: InfInteger -> BitStream -> PERMonad ()
add0s (Val n) xs = do
                     tell xs
                     tell $ take (fromInteger n) [0,0..]
add0s _ _        = throwError (OtherError "Invalid number input -- MIN or MAX.")

rem0s :: InfInteger -> InfInteger -> BitStream -> PERMonad ()
rem0s (Val (n+1)) l xs
    = if last xs == 0
           then rem0s (Val n) l (init xs)
           else throwError (OtherError "Last value is not 0")
rem0s (Val 0) l xs
    = rem0s' l xs
rem0s _ _ _ = throwError (OtherError "Cannot remove a negative, MIN or MAX number of 0s.")

rem0s' :: InfInteger -> BitStream -> PERMonad ()
rem0s' l xs
    = if genericLength xs > l && last xs == 0
        then rem0s' l (init xs)
        else tell xs
\end{code}

{\em encodeConBS}  applies one of X.691 15.8-15.11.

Note that in the last case of {\em encodeConBS} the lower bound of the constraint is ignored.
This is becuase the lower bound does not affect these length encodings (X.691 10.9.3.5 Note).

\begin{code}

encodeConBS :: PrefixBit -> InfInteger -> InfInteger -> BitStream -> PERMonad ()
encodeConBS pb l u xs
    = if u == 0
             then   {- X691REF: 15.8 -}
                    do  tell pb
                        tell []
             else if u == l && u <= 65536
                       then {- X691REF: 15.9 and 15.10 -}
                            do
                              tell pb
                              tell xs
                       else if u <= 65536
                            then {- X691REF: 15.11 (ub set) -}
                                do tell pb
                                   encodeConstrainedInt ((fromInteger.genericLength) xs - l, u-l)
                                   tell xs
                            else {- X691REF: 15.11 (ub unset) -}
                                do
                                    tell pb
                                    encodeBitsWithLength xs

\end{code}


{\em encodeNonExtRootBitstring} is similar to {\em encodeExtRootBitstring} but needs the
extension constraint and encodes the length of the bitstring as a semi-constrained whole
number with the lower bound set to zero as specified by X.691 15.11 and the note associated with
X.691 10.9.3.5.

Note that when pre-processing the bitstring in the named bits case, the upper and lower bound
of the constraint is generated from the union of the root and non-root constraint using our
{\em Lattice} class function {\em ljoin}. The {\em Lattice class}, related classes and class
instantiations are defined in the module {\em LatticeMod}.

\begin{code}

encodeNonExtRootBitstring :: NamedBits -> IntegerConstraint
        -> IntegerConstraint -> ValidIntegerConstraint -> BitStream -> PERMonad ()
encodeNonExtRootBitstring [] rc ec (Valid erc) xs
    | inSizeRange xs erc
        = do tell [1]
             encodeBitsWithLength xs
    | otherwise = throwError (BoundsError "Size out of range")
encodeNonExtRootBitstring nbs rc ec (Valid erc) xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
      in do
          (v,bs) <- return $ extractValue $ namedBitsEdit l u xs
          tell [1]
          encodeC encodeBitsWithLength (v,bs)

\end{code}



\subsection{First Refactoring}

\begin{code}

encodeBitString ::  NamedBits -> [SubtypeConstraint BitString] -> BitString -> AMonad ()

encodeBitString nbs [] x =
   encodeLargeLengthDeterminant chunkBy1 undefined (bitString x) -- FIXME: We are ignoring named bits!

encodeBitString nbs cl x =
   do Valid vc  <- validConstraint -- FIXME: Nasty pattern match. We should use something like data Valid = Valid { valid :: ... }
                                    -- and then we could say e.g. vc <- validConstraint >>= valid
      Valid vec <- validExtensionConstraint
      ec  <- effectiveConstraint
      eec <- effectiveExtensionConstraint
      isE <- isExtensibleConstraint
      let bs            = bitString x
          isInRoot      = inSizeRange bs vc
          isInExtension = inSizeRange bs vec
          doit
             | isE && (ec == bottom || eec== bottom) =
                  throwError (OtherError "encodeBitString: Empty constraint")
             | isE && isInRoot =
                  do tell . return $ 0
                     encodeLengthDeterminant (ec `ljoin` eec) chunkBy1 undefined bs
             | isE && isInExtension =
                  do tell . return $ 1
                     encodeLengthDeterminant (ec `ljoin` eec) chunkBy1 undefined bs
             | isE =
                  throwError (ConstraintError "encodeBitString: Value out of range")
             | ec == bottom =
                  throwError (OtherError "encodeBitString: Empty constraint")
             | isInRoot =
                  encodeLengthDeterminant ec chunkBy1 undefined bs
             | otherwise =
                  throwError (ConstraintError "encodeBitString: Value out of range")
      doit

   where effectiveConstraint :: AMonad IntegerConstraint -- FIXME: These probably shouldn't be monadic; they can and should be pure.
                                                         -- Or maybe not since "constraints" is monadic!!!
         effectiveConstraint = constraints cl >>= return . conType . getBSRC
         validConstraint :: AMonad ValidIntegerConstraint
         validConstraint = constraints cl >>= return . conType . getBSRC
         isExtensibleConstraint ::  AMonad Bool
         isExtensibleConstraint = integerConstraints cl >>= return . extensibleBS
         -- FIXME: This is slightly odd having to pick a type by hand.
         -- We really shouldn't need to do this.
         integerConstraints :: [SubtypeConstraint BitString] -> AMonad (ExtBS (ConType IntegerConstraint))
         integerConstraints = constraints
         effectiveExtensionConstraint :: AMonad IntegerConstraint
         effectiveExtensionConstraint = constraints cl >>= return . conType . getBSEC
         validExtensionConstraint :: AMonad ValidIntegerConstraint
         validExtensionConstraint = constraints cl >>= return . conType . getBSEC


chunkBy1 _ x = mapM_ (tell . return) x -- FIXME: We shouldn't ultimately need "return".

\end{code}

\section{ENCODING THE OCTETSTRING TYPE}

{\em encodeOctetstring} takes the usual two inputs -- the list of serially applied constraints
and the value to be encoded. If the constraint list is empty the function
{\em encodeUnconstrainedOctetstring} is
called. Otherwise, {\em encodeOctetstringWithConstraint} is called. Note that there are two ways
in which a OCTETSTRING type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible since a non-PER visible complete constraint is ignored.
This is determined when generating the effective constraint
for a type using the function {\em lSerialEffCon} defined in the module {\em ConstraintGeneration}.


\begin{code}

encodeOctetstring :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOctetstring [] x
    = {- X691REF: 16.8 with ub unset -}
      encodeUnconstrainedOctetstring x
encodeOctetstring cs x
    = {- X691REF: 16.3 -}
      encodeOctetstringWithConstraint cs x

exBS3 = extractValue $ encode (BuiltinType OCTETSTRING)
           [NonEmptyExtension (UnionSet (UC (IC (ATOM (E (SZ (SC (RootOnly
                        (UnionSet (IC (ATOM (E (V (R (1,5)))))))))))))
                                 (ATOM (E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R
                                    (7,10))))))))))))))
                        (UnionSet (UC (IC (ATOM (E (SZ (SC (RootOnly
                        (UnionSet (IC (ATOM (E (V (R (11,15)))))))))))))
                                 (ATOM (E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R
                                    (17,20))))))))))))))]
                                        (OctetString [1,0,1,1,0,0,1,0,1,1,0,1,0,0,0,0,0,0,0,1])
\end{code}


{\em encodeUnconstrainedOctetstring} encodes an unconstrained octetstring, It uses {\em
encodeUnconstrainedLength} -- which manages the interleaving of length encoding with value
encoding for values with an unconstrained length - whose first input {\em encodeOctet}
converts a {\em Word8} representation of an octet to a list of bits representation.

\begin{code}

encodeUnconstrainedOctetstring :: OctetString -> PERMonad ()
encodeUnconstrainedOctetstring (OctetString xs)
    = encodeUnconstrainedLength encodeOctet xs

encodeOctet :: Octet -> PERMonad ()
encodeOctet x = encodeConstrainedInt ((fromIntegral x),255)

\end{code}

If the constraint is not extensible then {\em encodeNonExtConsOctetstring} is called. If it is
extensible then {\em encodeExtConsOctettring} is called. They both take the effective
constraint and actual constraint associated with the type as input.

\begin{code}

encodeOctetstringWithConstraint :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOctetstringWithConstraint cs v
    = if (not extensible)
        then {- X691REF: 16.4 -}
             encodeNonExtConsOctetstring validCon effCon v
        else {- X691REF: 16.3 -}
             encodeExtConsOctetstring validCon effCon v
      where
          effCon :: Either String (ExtBS (ConType IntegerConstraint))
          effCon = lSerialEffCons lOSConE top cs
          validCon :: Either String (ExtBS (ConType ValidIntegerConstraint))
          validCon = lSerialEffCons lOSConE top cs
          extensible = eitherExtensible effCon

\end{code}

{\em encodeNonExtConsOctetstring} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedBitstring} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedOctetstring} is called.
\end{itemize}

\begin{code}

encodeNonExtConsOctetstring :: Either String (ExtBS (ConType ValidIntegerConstraint))
                -> Either String (ExtBS (ConType IntegerConstraint))
                -> OctetString
                -> PERMonad ()
encodeNonExtConsOctetstring _ (Right (ExtBS (ConType (IntegerConstraint NegInf PosInf)) _ _))
            (OctetString vs)
    =   {- X691REF: 16.8 with ub unset -}
        encodeUnconstrainedOctetstring (OctetString vs)
encodeNonExtConsOctetstring (Right ok) (Right vsc) (OctetString vs)
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = {- X691REF: 16.5 - 16.8 -}
             encodeConstrainedOctetstring [] l u vrc vs
             where
                rc = conType . getRC $ vsc
                l = lower rc
                u = upper rc
                vrc = conType . getRC $ ok

\end{code}

{\em encodeExtConsOctetstring} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedOctetstring} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedOctetstring} is called with the
prefix bit set to 0.
If this results in an error (the value cannot satisfy the constraint root) then {\em
encodeExtConstrainedOctetstring} is called and the prefix bit is set to 1. The function Haskell library function {\em catchError}
manages the error/non-error cases.
\end{itemize}


\begin{code}

encodeExtConsOctetstring :: Either String (ExtBS (ConType ValidIntegerConstraint))
                -> Either String (ExtBS (ConType IntegerConstraint))
                -> OctetString
                -> PERMonad()
encodeExtConsOctetstring _
    (Right (ExtBS (ConType (IntegerConstraint NegInf PosInf))
                  (ConType (IntegerConstraint NegInf PosInf)) _)) vs
    =   {- X691REF: 16.8 with ub unset -}
        encodeUnconstrainedOctetstring vs
encodeExtConsOctetstring (Right ok) (Right vsc) (OctetString vs)
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = do
                catchError (do {- X691REF: 16.3 within root -}
                               encodeConstrainedOctetstring [0] l u vrc vs)
                           (\err -> do {- X691REF: 16.3 not in root -}
                                       encodeNonExtRootConOctetstring rc ec vec vs)
             where
                rc = conType . getRC $ vsc
                l = lower rc
                u = upper rc
                ec = conType . getEC $ vsc
                vrc = conType . getRC $ ok
                vec = conType . getEC $ ok

\end{code}

{\em encodeConstrainedOctetstring} first checks if the value satisfies the constraint.

Note that X.691 16.5 states that if an octetstring is constrained to be of zero length then
it shall not be encoded. It is not clear whether this means that an octetstring with no length is
not encoded, or if any octetstring associated with a bitstring type with a zero-length
constraint is not encoded. We have implemented it using the former case. That is, the
octetstring must satisfy the constraint.

\begin{code}

encodeConstrainedOctetstring :: PrefixBit -> InfInteger -> InfInteger -> ValidIntegerConstraint ->
                                OctetStream -> PERMonad ()
encodeConstrainedOctetstring pb l u (Valid vrc) xs
      | inSizeRange xs vrc
         = let exs = encodeOctets xs
           in
             if u == 0
             then   {- X691REF: 16.5 -}
                    tell []
             else if u == l && u <= 65536
                       then {- X691REF: 16.6 and 16.7 -}
                            exs
                       else if u <= 65536
                            then {- X691REF: 16.8 (ub set) -}
                                 let (_,ls) = extractValue $ exs
                                 in do encodeConstrainedInt ((fromInteger.genericLength) ls - l, u-l)
                                       exs
                            else {- X691REF: 16.8 (ub unset) -}
                                 let (_,ls) = extractValue $ exs
                                 in
                                    encodeOctetsWithLength ls
       | otherwise = throwError (BoundsError "Size out of range")

encodeOctets :: OctetStream -> PERMonad ()
encodeOctets (x:xs)
         = mapM_ encodeOctet (x:xs)
encodeOctets [] = tell []

encodeNonExtRootConOctetstring :: IntegerConstraint -> IntegerConstraint
                                   -> ValidIntegerConstraint -> OctetStream -> PERMonad ()
encodeNonExtRootConOctetstring rc ec (Valid erc) xs
    | inSizeRange xs erc
        = let (_,ls) = extractValue $ encodeOctets xs
          in do tell [1]
                encodeOctetsWithLength ls
    | otherwise = throwError (BoundsError "Size out of range")

\end{code}

\section{ENCODING THE SEQUENCE TYPE}

{\em encodeSequence} has only two inputs - the type and value - since a sequence has no PER-visible
constraints. It calls an auxilliary function {\em encodeSequenceAux} which requires two
further inputs which indicate the extensibility of the type and existence of extension
additions (represented as a pair of boolean values), and hosts the bits which indicate the presence or otherwise of optional or default
values. {\em encodeSequenceAux} is a recursive function that recurses over the structure of a sequence.
It has several cases to deal with that match the various components of a sequence -- mandatory, optional,
default, extension marker and so on -- and
returns a pair whose second component is the function
{\em completeSequenceBits} which adds a prefix to the output bits including the extension bit if
required and the bits which describe the presence or otherwise of optional or default values.
Each root component is encoded as required using {\em encode} and if the type has any extesnion additions
these are encoded by the {\em encodeSequenceAux}.
The Haskell {\em MonadWriter} function {\em pass} applies this
function to the output bits.

Note that the extension indicator is initally set to {\em (False, False)}. The first element is converted
to {\em True} when an extension marker is reached and {\em encodeSequenceAuxExt} is called and
its bits output in advance of {\em encodeSequenceAux} continuing its recursive progress.
{\em encodeSequenceAuxExt} produces the encoding of the any extension additions including the
required preamble. If the type includes a second extesnion marker then the {\em
encodeSequenceAux} simply continues recursing through the type.

Note also that the encoding of a {\em COMPONENTS OF} item is managed by
{\em encodeSequenceAuxCO}.

\begin{code}
type OptDefBits = BitStream
type ExtBits = BitStream
type ExtAndUsed = (Bool, Bool)

axSeq = AddComponent (MandatoryComponent (NamedType "a" (ConstrainedType  (BuiltinType INTEGER) con1)))
                (AddComponent (MandatoryComponent (NamedType "b" (BuiltinType BOOLEAN)))
                    (AddComponent (MandatoryComponent (NamedType "c" (BuiltinType (CHOICE choice1))))
                        (ExtensionMarker
                          (ExtensionAdditionGroup NoVersionNumber eag1
                           (ExtensionMarker (AddComponent (OptionalComponent (NamedType "i" (BuiltinType BMPSTRING)))
                                (AddComponent (OptionalComponent (NamedType "j" (BuiltinType PRINTABLESTRING)))
                                    EmptySequence)))))))

choice1 = ChoiceOption (NamedType "d" (BuiltinType INTEGER))
            (ChoiceExtensionMarker (ChoiceExtensionAdditionGroup NoVersionNumber
                            (ChoiceOption (NamedType "e" (BuiltinType BOOLEAN))
                                   (ChoiceOption (NamedType "f"  (BuiltinType IA5STRING))
                                          (ChoiceExtensionAdditionGroup NoVersionNumber (ChoiceExtensionMarker EmptyChoice))))))


eag1 = AddComponent (MandatoryComponent (NamedType "g" (ConstrainedType  (BuiltinType NUMERICSTRING) (RootOnly pac5))))
        (AddComponent (OptionalComponent (NamedType "h" (BuiltinType BOOLEAN))) EmptySequence)

pac5 = UnionSet (IC (ATOM ((E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R (3,3))))))))))))))

con1 = RootOnly (UnionSet (IC (ATOM (E (V (R (250,253)))))))

axVal2 = Val 253 :*:
        (True :*:
            ((AddNoValue NoValue (AddAValue True (AddNoValue NoValue EmptyList))) :*:
                    ((Just ((NumericString "123") :*: (Just True :*: Empty))) :*:
                        (Just (BMPString "A") :*: (Nothing :*: Empty)))))


axVal = Val 253 :*:
        (True :*:
            ((AddNoValue NoValue (AddAValue True (AddNoValue NoValue EmptyList))) :*:
                    ((Just ((NumericString "123") :*: (Just True :*: Empty))) :*:
                        (Nothing :*: (Nothing :*: Empty)))))


ns1 :: SubtypeConstraint VisibleString
ns1 = RootOnly (UnionSet (IC (ATOM ((E (SZ (SC (RootOnly (UnionSet (IC (ATOM (E (V (R(1,1)))))))))))))))

encodeSequence :: Sequence a -> a -> PERMonad ()
encodeSequence s v = do odb <- pass $ encodeSequenceAux (False, False) [] s v
                        return ()

encodeSequenceAux :: ExtAndUsed -> OptDefBits -> Sequence a -> a
                -> PERMonad (OptDefBits, BitStream -> BitStream)
encodeSequenceAux eu od EmptySequence Empty
    = return (od, completeSequenceBits eu od)
encodeSequenceAux (extensible, b) od (ExtensionMarker as) xs
    | not extensible
        = let m = encodeSequenceAuxExt (True, False) od [] as xs
          in
           do (b, eb, od, pm) <- censor (const []) m
              (od2,f) <- pm
              censor ((++) (snd . extractValue $ lengthAddsNew eb)) m
              encodeSequenceAux b od2 EmptySequence Empty
    | otherwise
        = encodeSequenceAux (extensible,b) od as xs
encodeSequenceAux eu od (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
{- NOTE: od2 is the optional/default list of the components of a sequence -}
    = do od2 <- encodeSequenceAuxCO [] s x
         encodeSequenceAux eu (od ++ od2) as xs
encodeSequenceAux eu od (AddComponent (ComponentsOf (ReferencedType n t)) as) (x:*:xs)
    = encodeSequenceAux eu od (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSequenceAux eu od (AddComponent (ComponentsOf (ConstrainedType t c)) as) (x:*:xs) -- typically a reference
    = encodeSequenceAux eu od (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSequenceAux eu od (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do
        encode a [] x
        encodeSequenceAux eu od as xs
encodeSequenceAux eu od (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    = encodeSequenceAux eu od as xs
encodeSequenceAux (b1,b2) od (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = encodeSequenceAux (b1, True) od as xs
encodeSequenceAux eu od (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with optional component not present -}
        encodeSequenceAux eu (od ++ [0]) as xs
encodeSequenceAux eu od (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.2 with optional comonent present -}
         encode a [] x
         encodeSequenceAux eu (od ++ [1]) as xs
encodeSequenceAux eu od (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with default component not present -}
        encodeSequenceAux eu (od ++ [0]) as xs
encodeSequenceAux eu od (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do {- X691REF: 18.2 with default component present -}
         encode a [] x
         encodeSequenceAux eu (od ++ [1]) as xs
encodeSequenceAux (b1,b2) od (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeSequenceAux (b1,True) od as xs


completeSequenceBits :: ExtAndUsed -> OptDefBits -> BitStream -> BitStream
completeSequenceBits (extensible, extensionAdditionPresent) odb bs
    | not extensible
        = odb ++ bs
    | extensionAdditionPresent
        {- X691REF: 18.1 with extension additions present -}
        {- X691REF: 18.2  -}
        = 1: odb ++ bs
    | otherwise
        {- X691REF: 18.1 with no extenion additions present -}
        {- X691REF: 18.2  -}
        = 0: odb ++ bs

encodeSequenceAuxExt :: ExtAndUsed -> OptDefBits -> ExtBits -> Sequence a -> a
                        -> PERMonad ((ExtAndUsed, ExtBits, OptDefBits, PERMonad (OptDefBits, BitStream -> BitStream)))
encodeSequenceAuxExt b odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    = encodeSequenceAuxExt b odb (eb ++ [0]) as xs
encodeSequenceAuxExt (b1,b2) odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do encodeOpen a x
         encodeSequenceAuxExt (b1,True) odb (eb ++ [1]) as xs
encodeSequenceAuxExt b odb eb (ExtensionAdditionGroup _ a as) (Nothing:*:xs)
    = encodeSequenceAuxExt b odb (eb ++ [0]) as xs
encodeSequenceAuxExt (b1,b2) odb eb (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do encodeOpen (BuiltinType (SEQUENCE a)) x
         encodeSequenceAuxExt (b1, True) odb (eb ++ [1]) as xs
encodeSequenceAuxExt b odb eb (ExtensionMarker as) xs
    = return (b, eb, odb, encodeSequenceAux b odb as xs)
encodeSequenceAuxExt b odb eb EmptySequence Empty
    | null eb
        = return (b, eb, odb, encodeSequenceAux b odb EmptySequence Empty)
    | otherwise
        = return (b, eb, odb, encodeSequenceAux b odb EmptySequence Empty)
encodeSequenceAuxExt b odb eb _ _
    = throwError (OtherError "Inappropriate component!")

\end{code}

{- FIXME:I DON'T THINK THAT THE ELSE CASE IS FRAGMENTING CORRECTLY -}

18.8 A length determinant of the number of extension additions is added if
the sequence has any extension additions declared. This is encoded as a normally
small length (10.9.3.4)


\begin{code}

lengthAddsNew ap
    = let la = genericLength ap
       in if la <= 63
        then do tell [0]
                encodeConstrainedInt (la-1, 63)
                tell ap
        else do tell [1]
                encodeOctetsWithLength (encodeNonNegBinaryIntInOctets la)
                tell ap

{- X.680 24.4 -}

encodeSequenceAuxCO :: OptDefBits -> Sequence a -> a -> PERMonad OptDefBits
encodeSequenceAuxCO odb EmptySequence _
    = return odb
encodeSequenceAuxCO odb (ExtensionMarker as) xs
    = encodeSequenceAuxCO odb as xs
encodeSequenceAuxCO odb (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do odb2 <- encodeSequenceAuxCO [] s x
         encodeSequenceAuxCO (odb ++ odb2) as xs
encodeSequenceAuxCO odb (AddComponent (ComponentsOf _) as) (x:*:xs)
    = throwError (OtherError "COMPONENTS OF can only be applied to a SEQUENCE")
encodeSequenceAuxCO odb (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do encode a [] x
         encodeSequenceAuxCO odb as xs
encodeSequenceAuxCO odb (AddComponent (ExtensionComponent (NamedType t a)) as) (_:*:xs) =
   encodeSequenceAuxCO odb as xs
encodeSequenceAuxCO odb (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeSequenceAuxCO (odb ++ [0]) as xs
encodeSequenceAuxCO odb (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        encode a [] x
        encodeSequenceAuxCO (odb ++ [1]) as xs
encodeSequenceAuxCO odb (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    = encodeSequenceAuxCO (odb ++ [0]) as xs
encodeSequenceAuxCO odb (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        encode a [] x
        encodeSequenceAuxCO (odb ++ [1]) as xs
encodeSequenceAuxCO odb (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeSequenceAuxCO odb as xs

\end{code}

\section{Refactoring Stuff}

Conversion functions for use during refactoring so
we don't have to change everything all at once.

\begin{code}

temporaryConvert :: Monoid x => Either String x -> ErrorT ASNError (WriterT x Identity) ()
temporaryConvert (Left s) = throwError (OtherError s)
temporaryConvert (Right x) = tell x

type AMonad a = ErrorT ASNError (WriterT BitStream Identity) a

constraints :: (Eq a, Show a, Lattice a, IC a) => [SubtypeConstraint BitString] -> AMonad (ExtBS (ConType a))
constraints cs = errorize (lSerialEffCons lBSConE top cs)

errorize :: (MonadError ASNError m) => Either String a -> m a
errorize (Left e)  = throwError (ConstraintError e)
errorize (Right x) = return x

\end{code}

\section{Length Determinants}

\begin{code}

encodeLengthDeterminant ::
  IntegerConstraint -> (ASNType a -> [a] -> DomsMonad) -> (ASNType a -> [a] -> DomsMonad)
encodeLengthDeterminant c f t xs
   | ub /= maxBound &&
     ub == lb &&
     ub <= 64*(2^10) = f t xs
   | ub > 64*(2^10) = encodeLargeLengthDeterminant f t xs {- FIXME: A word of explanation as to why
                                                             we test this here - it's because after
                                                             here we know y is defined. -}
   | ub <= 64*(2^10) {- 10.9.1 -}
        = do constrainedWholeNumber c y
             f t xs
   | otherwise      = error "FIXME: encodeLengthDeterminant"
   where
      ub = upper c
      lb = lower c
      y  = genericLength xs

constrainedWholeNumber :: IntegerConstraint -> Integer -> DomsMonad
constrainedWholeNumber c v =
   encodeInt [rangeConstraint (lb,ub)] (Val v)
   where
      ub = upper c
      lb = lower c
      rangeConstraint :: (InfInteger, InfInteger) -> ElementSetSpecs InfInteger
      rangeConstraint =  RootOnly . UnionSet . IC . ATOM . E . V . R

\end{code}

Note: We can use length safely (rather than genericLength) in the cases where we know
the arguments are sufficiently small (in particular we know we have blocks of 4 or less of
blocks of $16(2^{10})$ or less).

\begin{code}
encodeLargeLengthDeterminant ::
  (ASNType a -> [a] -> DomsMonad) -> ASNType a -> [a] -> DomsMonad
encodeLargeLengthDeterminant f t xs = doit
   where
      doit
         | {- X691REF: 10.9.3.6 -} l < 128       = h l >> f t xs
         | {- X691REF: 10.9.3.7 -} l < 16*(2^10) = h l >> f t xs
         | {- X691REF: 10.9.3.8 -} otherwise     = if isFullBlock 4
                                                      then fullBlock
                                                      else doFirstTrue possibleBlocks
      ysss            = groupBy 4 (groupBy (16*(2^10)) xs)
      (hsss, tsss)    = genericSplitAt 1 ysss
      hss             = concat hsss
      isFullBlock n   = length hss == n && length (hss!!(n-1)) == 16*(2^10)
      l               = genericLength xs
      h               = temporaryConvert . return . encodeNonNegBinaryIntInOctets
      fullBlock       = do h (fromIntegral 4)
                           f t (concat hss)
                           encodeLargeLengthDeterminant f t (concat . concat $ tsss)
      partialBlock n  = do h (fromIntegral n)
                           f t (concat (take n hss))
                           encodeLargeLengthDeterminant f t (concat (drop n hss))
      possibleBlocks  = map (\n -> (isFullBlock n, partialBlock n)) [3..1]
      doFirstTrue :: Monad m => [(Bool, m ())] -> m ()
      doFirstTrue []          = return ()
      doFirstTrue ((p,a):pas) = if p then a else doFirstTrue pas

\end{code}

\section{ENCODING THE SEQUENCE-OF TYPE}

\subsection{Dom's Refactored Version}

\begin{code}

{- FIXME: We may want this to be "a" rather than always () -}
type DomsMonad = ErrorT ASNError (WriterT BitStream Identity) ()

{- FIXME: I think SubtypeConstraint [a] needs a word of explanation that -}
{- we are constraining the list not the type. Also, would it be better   -}
{- have our own (Haskell) type rather than [a]?                          -}
encodeSequenceOf :: ASNType a -> [SubtypeConstraint [a]] -> [a] -> DomsMonad
encodeSequenceOf t [] xs =
   encodeLargeLengthDeterminant nSequenceOf t xs
encodeSequenceOf t cs xs =
   encodeSequenceOfAux t (errorize (effSeqOfCon cs)) (errorize (validSeqOfCon cs)) xs

encodeSequenceOfAux t me mv xs =
   do e <- me
      v <- mv
      let rc = conType . getBSRC $ e
      encodeLengthDeterminant rc nSequenceOf t xs

nSequenceOf :: ASNType a -> [a] -> DomsMonad
nSequenceOf t xs = mapM_ (encode t []) xs

\end{code}

\subsection{Original Version}

encodeSO implements the encoding of an unconstrained
sequence-of value. This requires both the encoding of
each of the components, and in most cases the encoding
of the length of the sequence-of (which may require
fragmentation into 64K blocks).

\begin{code}

encodeSeqOf :: [SubtypeConstraint [a]] -> ASNType a -> [a] -> PERMonad ()
encodeSeqOf [] t x = encodeUncSeqOf t x
encodeSeqOf cl t x = encodeConSeqOf t cl x


\end{code}

encodeUncSeqOf encodes an unconstrained SEQUENCEOF value.

\begin{code}

encodeUncSeqOf :: ASNType a -> [a] -> PERMonad ()
encodeUncSeqOf t xs = mEncodeWithLength (encodeList t) xs

mEncodeWithLength :: ([[t]] -> PERMonad ()) -> [t] -> PERMonad ()
mEncodeWithLength fun xs
    = let ls = (groupBy 4 . groupBy (16*(2^10))) xs
      in  mencodeUnconstrainedLength fun ls


mencodeUnconstrainedLength :: ([[b]] -> PERMonad ()) -> [[[b]]] -> PERMonad ()
mencodeUnconstrainedLength encFun [] = lengthLessThan16K 0
mencodeUnconstrainedLength encFun (x:xs)
    | l == 4 && last16 == k16
        = do
            blockLen 4 63
            encFun x
            mencodeUnconstrainedLength encFun xs
    | l == 1 && last16 < k16
        = do
            lengthLessThan16K ((genericLength . head) x)
            encFun ([head x])
    | last16 == k16
        = do
            blockLen l 63
            encFun x
            lengthLessThan16K 0
    | otherwise
        = do
            blockLen (l-1) 63
            encFun (init x)
            lengthLessThan16K ((genericLength.last) x)
            encFun ([last x])
    where
        l      = genericLength x
        last16 = (genericLength . last) x

\end{code}


\begin{code}

encodeConSeqOf :: ASNType a -> [SubtypeConstraint [a]] -> [a] -> PERMonad ()
encodeConSeqOf t cl xs = lEncValidSeqOf t (effSeqOfCon cl) (validSeqOfCon cl) xs

effSeqOfCon ::[SubtypeConstraint [a]] -> Either String (ExtBS (ConType IntegerConstraint))
effSeqOfCon cs = lSerialEffCons lSeqOfConE top cs


validSeqOfCon :: [SubtypeConstraint [a]] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validSeqOfCon cs = lSerialEffCons lSeqOfConE top cs


lEncValidSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> [a] -> PERMonad ()
lEncValidSeqOf t m@(Right vsc) n v
    = if extensibleBS vsc
            then lEncExtSeqOf t m n v
            else lEncNonExtSeqOf t m n v
lEncValidSeqOf _ (Left s) _ _
    = throwError (ConstraintError s)

lEncNonExtSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> [a]
                -> PERMonad ()
lEncNonExtSeqOf t (Right vsc) (Right ok) vs
       | isEmptyConstraint rc
            = throwError (ConstraintError "Empty constraint")
       | inSizeRange vs okrc
            = soCode rc t vs
       | otherwise
            = throwError (BoundsError "Value out of range")
              where rc = conType . getBSRC $ vsc
                    Valid okrc = conType . getBSRC $ ok

soCode rc t xs
      =  let l  = lower rc
             u  = upper rc
         in
             if u == l && u <= 65536
                       then encodeAll t xs
                       else if u <= 65536
                            then do
                                     encodeConstrainedInt (((fromInteger.genericLength) xs-l), (u-l))
                                     encodeAll t xs
                            else do
                                    mEncodeWithLength (encodeList t) xs


soExtCode rc ec t xs
      =  let nc = rc `ljoin` ec
             l  = lower nc
             u  = upper nc
         in
            if u <= 65536
                            then do
                                     encodeConstrainedInt (((fromInteger.genericLength) xs-l), (u-l))
                                     encodeAll t xs
                            else do
                                    mEncodeWithLength (encodeList t) xs


encodeList :: ASNType a -> [[a]] -> PERMonad ()
encodeList t []
    = tell []
encodeList t (f:r)
    = do
        encodeAll t f
        encodeList t r

encodeAll :: ASNType a -> [a] -> PERMonad ()
encodeAll t (f:r)
    = let (_,x) = extractValue (encode t [] f)
      in do tell x
            encodeAll t r
encodeAll t [] = tell []


lEncExtSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> [a]
                -> PERMonad ()
lEncExtSeqOf t (Right vsc) (Right ok) vs
        | isEmptyConstraint rc
              = throwError (ConstraintError "Empty constraint")
        | inSizeRange vs okrc
              = do
                  tell [0]
                  soCode rc t vs
        | inSizeRange vs okec
              = do tell [1]
                   soExtCode rc ec t vs
        | otherwise
              = throwError (BoundsError "Value out of range")
                where rc = conType . getBSRC $ vsc
                      Valid okrc = conType . getBSRC $ ok
                      ec = conType . getBSEC $ vsc
                      Valid okec = conType . getBSEC $ ok

\end{code}


\section{ENCODING THE SET TYPE}

Encoding the SET type. The encoding is the same as for a
SEQUENCE except that the components must be canonically ordered.
The ordering is based on the component's tags. Note, the
preamble must be reordered to match the ordering of the
components.

\begin{code}

encodeSet :: Sequence a -> a -> PERMonad ()
encodeSet s x = tell []
{- FIXME: To fix!!
    =   do
            ((rp,rb),(ap,ab)) <- encodeSeqAux ([],[]) ([],[]) s x
            let ts  = getTags s
                ps  = zip ts rb
                pps = zip rp ps
                os  = mergesort setPred pps
                pr  = concat (map fst os)
                en  = concat (map (snd . snd) os)
            return (pr ++ en ++ concat ap ++ concat ab)
-}
\end{code}



 Sorting predicate and tag selector

\begin{code}

setPred :: (BitStream,(TagInfo, BitStream)) -> (BitStream,(TagInfo, BitStream)) -> Bool
setPred (_,(t1,_)) (_,(t2,_)) = t1 < t2

tagOrder :: ASNType a -> ASNType a -> Bool
tagOrder x y = getTI x < getTI y


getTags :: Sequence a -> [TagInfo]
getTags EmptySequence               = []
getTags (ExtensionMarker xs)       = getTags' xs
getTags (AddComponent a xs)       = getCTI a : getTags xs
getTags (ExtensionAdditionGroup _ _ _)         = error "Impossible case for a root component."



getTags' :: Sequence a -> [TagInfo]
getTags' EmptySequence         = []
getTags' (ExtensionMarker xs) = getTags xs
getTags' (AddComponent a xs) = getTags' xs
getTags' (ExtensionAdditionGroup _ s t)   = getTags' t

\end{code}



\section{ENCODING THE CHOICE TYPE}

encodeChoice encodes CHOICE values. It is not dissimilar to
encodeSet in that the possible choice components must be
assigned an index based on their canonical ordering. This index,
which starts from 0, prefixes the value encoding and is absent if
there is only a single choice. The auxillary function
encodeChoiceAux deals with the possible cases, and
encodeChoiceAux' is called once a value has been encoded to ensure
that only one choice value is encoded.

\begin{code}

encodeChoice :: Choice a -> ExactlyOne a SelectionMade -> PERMonad ()
encodeChoice c x
   = let ts = getCTags c
     in case (encodeChoiceAux [] [] c x) of
         Right (ea, ec) ->
           if length ec == 1
             then mapM_ tell ec
             else
                let ps  = zip ts ec
                    os  = mergesort choicePred ps
                    pps = zip [0..] os
                    fr  = (head . filter (not . nullValue)) pps
                    ls  = genericLength os
                in
                 if null ea
                    then do encodeConstrainedInt (fromInteger $ fst fr,fromInteger $ ls-1)
                            tell $ (snd .snd) fr
                    else
                       if length ec <= 63
                       then do tell ea
                               tell [0]
                               encodeConstrainedInt (fromInteger $ fst fr, fromInteger 63)
                               tell $ (snd.snd) fr
                       else do tell ea
                               tell [1]
                               encodeOctetsWithLength (encodeNonNegBinaryIntInOctets (fromInteger $ fst fr))
                               tell $ (snd.snd) fr
         Left s -> throwError (OtherError s)

\end{code}

 IS THE ELSE CASE ABOVE CORRECT???

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
splitrec (x1:x2:xs) [] zs = error "Impossible case when used by split"

merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge pred xs [] = xs
merge pred [] ys = ys
merge pred (x:xs) (y:ys)
    = case pred x y
        of True -> x: merge pred xs (y:ys)
           False -> y: merge pred (x:xs) ys


nullValue :: (Integer, (TagInfo, BitStream)) -> Bool
nullValue (f,(s,t)) = null t


choicePred :: (TagInfo, BitStream) -> (TagInfo, BitStream) -> Bool
choicePred (t1,_) (t2,_) = t1 <= t2


encodeChoiceAux :: [Int] -> [BitStream] -> Choice a -> ExactlyOne a n ->  Either String ([Int], [BitStream])
encodeChoiceAux ext body EmptyChoice _ = return (ext, reverse body)
encodeChoiceAux ext body (ChoiceExtensionMarker as) xs =
   encodeChoiceExtAux [0] body as xs
encodeChoiceAux ext body (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceAux ext ([]:body) as xs
encodeChoiceAux ext body (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeChoiceAux' ext (bts:body) as xs
encodeChoiceAux _ _ (ChoiceExtensionAdditionGroup _ _) _
    = throwError "Impossible case: EXTENSION ADDITON GROUP only appears in an extension."


encodeChoiceAux' :: [Int] -> [BitStream] -> Choice a -> ExactlyOne a n -> Either String ([Int], [BitStream])
encodeChoiceAux' ext body EmptyChoice _ = return (ext, reverse body)
encodeChoiceAux' ext body (ChoiceExtensionMarker as) xs =
   encodeChoiceExtAux' ext body as xs
encodeChoiceAux' ext body (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceAux' ext ([]:body) as xs
encodeChoiceAux' ext body (ChoiceOption a as) (AddAValue x xs) =
   encodeChoiceAux' ext ([]:body) as xs
encodeChoiceAux' _ _ (ChoiceExtensionAdditionGroup _ _) _
    = throwError "Impossible case: EXTENSION ADDITON GROUP only appears in an extension."


encodeChoiceExtAux :: [Int] -> [BitStream] -> Choice a -> ExactlyOne a n -> Either String ([Int], [BitStream])
encodeChoiceExtAux ext body EmptyChoice _ = return (ext,reverse body)
encodeChoiceExtAux ext body (ChoiceExtensionMarker as) xs =
   encodeChoiceAux ext body as xs
encodeChoiceExtAux ext body (ChoiceExtensionAdditionGroup _ as) xs =
   encodeChoiceExtAux ext body as xs
encodeChoiceExtAux ext body (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceExtAux ext ([]:body) as xs
encodeChoiceExtAux ext body (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do (err,bts) <- return (extractValue (encodeOpen a x))
         encodeChoiceExtAux' [1](bts:body) as xs

encodeChoiceExtAux' :: [Int] -> [BitStream] -> Choice a -> ExactlyOne a n -> Either String ([Int], [BitStream])
encodeChoiceExtAux' ext body EmptyChoice _ = return (ext, reverse body)
encodeChoiceExtAux' ext body (ChoiceExtensionMarker as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceExtensionAdditionGroup _ as) xs =
   encodeChoiceAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceExtAux' ext body as xs
encodeChoiceExtAux' ext body (ChoiceOption a as) (AddAValue x xs) =
   encodeChoiceExtAux' ext body as xs


\end{code}

\section{ENCODING THE RESTRICTED CHARACTER STRING TYPES}

If the type is extensible then a single bit shall be added to the
encoding. This is set to 0 if the value is withing the range of
the extension root and to 1 otherwise. If the value is outside the
range then the encoding shall be as if there was no effective size
constraint and shall have an effective permitted alphabet
constraint that consists of the set of characters of the
unconstrained type.

The first case of encodeVisString is for an unconstrained value.
Note that a check on the validity of the string value is made
before any encoding.
\begin{code}

encodeRCS :: (Eq a, RS a, Lattice a)
              => SerialSubtypeConstraints a -> a -> PERMonad ()
encodeRCS [] vs
        | rcsMatch vs top
            = encodeResString vs
        | otherwise
            = throwError (BoundsError "Invalid value!")
encodeRCS cs vs
        | rcsMatch vs top
            = lEncValidRCS (effCon cs) (validCon cs) vs
        | otherwise
            = throwError (BoundsError "Invalid value!")


effCon :: (RS a, Lattice a, Eq a)
          => SerialSubtypeConstraints a -> Either String (ExtResStringConstraint (ResStringConstraint a IntegerConstraint))
effCon cs = lSerialEffCons lResConE top cs

validCon :: (RS a, Lattice a, Eq a)
            => SerialSubtypeConstraints a -> Either String (ExtResStringConstraint (ResStringConstraint a ValidIntegerConstraint))
validCon cs = lSerialEffCons lResConE top cs

-- The first case of encVS deals with non-per visible constraint.
-- If the constraint is non-per visible then we treat the value as
-- unconstrained.
-- NEED TO DEAL WITH CASE WHEN ROOT AND EXTENSION ARE DIFFERENT
-- CONSTRAINTS

rcsMatch :: RS a => a -> a -> Bool
rcsMatch x y = stringMatch (getString x) (getString y)

stringMatch [] s = True
stringMatch (f:r) s = elem f s && stringMatch r s


lEncValidRCS :: (RS a, Eq a, Lattice a) =>
                 Either String (ExtResStringConstraint (ResStringConstraint a IntegerConstraint))
                 -> Either String (ExtResStringConstraint (ResStringConstraint a ValidIntegerConstraint))
                 -> a -> PERMonad ()
lEncValidRCS m@(Right vsc) n v
    = if extensible vsc
            then lEncExtRCS m n v
            else lEncNonExtRCS m n v
lEncValidRCS (Left s) n v
    = throwError (ConstraintError s)


{-
A value is out of range if it is not within the constraint. This
includes the cases where either the size or PA constraint is
bottom which by default cannot be satisfied.
No constraint is represented by the lattice attribute top which is
the default value when generating an effective constraint.
-}

lEncNonExtRCS :: (RS a, Eq a, Lattice a) =>
                Either String (ExtResStringConstraint (ResStringConstraint a IntegerConstraint))
                -> Either String (ExtResStringConstraint (ResStringConstraint a ValidIntegerConstraint))
                -> a
                -> PERMonad ()
lEncNonExtRCS (Right vsc) (Right ok) vs
     | isEmptyConstraint rc
         = throwError (ConstraintError "Empty constraint")
     | not noSC && not noPAC && inPA pac && inSizeRange (getString vs) oksc
         = encodeRCSSzF sc pac vs
     | noSC && not noPAC && inPA pac
         = encodeRCSF pac vs
     | noPAC && not noSC && inSizeRange (getString vs) oksc
         = encodeRCSSz sc vs
     | otherwise
         = throwError (BoundsError "Value out of range")
           where
                rc = getRC vsc
                okrc = getRC ok
                sc = getSC rc
                Valid oksc = getSC okrc
                pac = getPAC rc
                noSC  = sc == top
                noPAC = pac == top
                inPA x  = stringMatch (getString vs) (getString x)


lEncExtRCS :: (RS a, Eq a, Lattice a) =>
              Either String (ExtResStringConstraint (ResStringConstraint a IntegerConstraint))
              -> Either String (ExtResStringConstraint (ResStringConstraint a ValidIntegerConstraint))
              -> a
              -> PERMonad ()
lEncExtRCS (Right vsc) (Right ok) vs
    =   let rc = getRC vsc
            ec = getEC vsc
            okrc = getRC ok
            okec = getEC ok
            rsc = getSC rc
            Valid okrsc = getSC okrc
            rpac = getPAC rc
            esc = getSC ec
            Valid okesc = getSC okec
            epac = getPAC ec
            concStrs :: RS a => ResStringConstraint a i ->
                                  ResStringConstraint a i -> a
            concStrs rc ec
                  = let r = (getString . getPAC) rc
                        e = (getString . getPAC) ec
                    in makeString (r++e)
            expac = concStrs rc ec
            noRC  = rc == top
            noEC  = ec == top
            noRSC  = rsc == top
            noRPAC = rpac == top
            noESC  = esc == top
            noEPAC = epac == top
            inPA x  = stringMatch (getString vs) (getString x)
            foobar
                | isEmptyConstraint rc
                    = throwError (ConstraintError "Empty constraint")
                | otherwise = foobarREC
            foobarREC
                | noEC = foobarRC
                | noRC = foobarEC
                | otherwise = foobarBoth
            foobarRC
                | noRSC && inPA rpac
                    = do tell [0]
                         encodeRCSF rpac vs
                | noRPAC && inSizeRange (getString vs) okrsc
                    = do tell [0]
                         encodeRCSSz rsc vs
                | inPA rpac && inSizeRange (getString vs) okrsc
                    = do tell [0]
                         encodeRCSSzF rsc rpac vs
                | otherwise
                    = throwError (BoundsError "Value out of range")
            foobarEC
                | noESC && inPA epac
                    = do tell [1]
                         encodeRCSF top vs
                | noEPAC && inSizeRange (getString vs) okesc
                    = do tell [1]
                         encodeResString vs
                | inPA epac && inSizeRange (getString vs) okesc
                    = do tell [1]
                         encodeRCSF top vs
                | otherwise
                    = throwError (BoundsError "Value out of range")
            foobarBoth
                | not noRPAC && inPA rpac && not noRSC && inSizeRange (getString vs) okrsc
                    = do tell [0]
                         encodeRCSSzF rsc rpac vs
                | noRPAC && noEPAC && not noRSC && inSizeRange (getString vs) okrsc
                    = do tell [0]
                         encodeRCSSz rsc vs
                | noRSC && noESC && not noRPAC && inPA rpac
                    = do tell [0]
                         encodeRCSF rpac vs
                | noRPAC && noEPAC && not noESC && inSizeRange (getString vs) okesc
                    = do tell [1]
                         encodeResString vs
                | (not noRSC && inSizeRange (getString vs) okrsc && noRPAC && not noEPAC &&
                   inPA epac) ||
                  (not noRSC && inSizeRange (getString vs) okrsc && not noRPAC && not noEPAC &&
                   not (inPA epac) && inPA expac) ||
                  (not noESC && inSizeRange (getString vs) okesc && not noRPAC && inPA rpac) ||
                  (not noESC && inSizeRange (getString vs) okesc && noRPAC && not noEPAC &&
                  inPA epac) ||
                  (not noESC && inSizeRange (getString vs) okesc && not noRPAC && not noEPAC &&
                  not (inPA epac) && inPA expac) ||
                  (noRSC && noESC && ((noRPAC && not noEPAC && inPA epac) ||
                  (not noRPAC && not noEPAC && not (inPA epac) && inPA expac)))
                     =  do tell [1]
                           encodeRCSF top vs
                | otherwise
                     = throwError (BoundsError "Value out of range")
        in foobar

encodeRCSSz :: (RS a, Lattice a) => IntegerConstraint -> a -> PERMonad ()
encodeRCSSz (IntegerConstraint l u) v
    = let t = getTop v
       in
        manageRCS (encSF (getString t)) makeString encodeResString getString l u v


manageRCS :: (RS a, Lattice a) => (String -> PERMonad ()) -> (String -> a) ->
                       (a -> PERMonad ()) -> (a -> String) -> InfInteger
                        -> InfInteger -> a -> PERMonad ()
manageRCS e f g h l u v
    = manageExtremes e (g . f) l u (h v)


encodeResString :: (RS a, Lattice a) => a -> PERMonad ()
encodeResString vs
    = let t = getTop vs
      in
         encodeWithLength top (encSF (getString t))  [(getString vs)] {- FIXME check top here -}

getTop :: (RS a, Lattice a) => a -> a
getTop m = top

encC :: Integer -> Char -> PERMonad ()
encC i c = encodeConstrainedInt (fromInteger $ (fromIntegral.ord) c, fromInteger i)

encS :: Integer -> String -> PERMonad ()
encS i s  = mapM_ (encC i) s

\end{code}

 27.5.4 Encoding of a RESTRICTED CHARACTER STRING with a permitted alphabet
 constraint.

\begin{code}

encodeRCSSzF :: (RS a) => IntegerConstraint -> a -> a -> PERMonad ()
encodeRCSSzF (IntegerConstraint l u) rcs1 rcs2
        =  manageExtremes (encSF (getString rcs1))
                          (encodeRCSF rcs1 . makeString) l u (getString rcs2)

encodeRCSF :: (RS a) => a -> a -> PERMonad ()
encodeRCSF rcs1 rcs2 = encodeWithLength top (encSF (getString rcs1)) [(getString rcs2)] {- FIXME check top here -}


encSF p str
    = let sp  = sort p
          lp  = genericLength p
          b   = minExp 2 0 lp
          mp  = maximum p
      in
        if ord mp < 2^b -1
            then
                encS lp str
            else
                canEnc (fromInteger $ lp-1) sp str


minExp n e p
    = if n^e < p
        then minExp n (e+1) p
        else e

-- The first two cases are described in X.691 27.5.6 and 25.5.7
-- and the last case by 10.9 Note 3.

manageExtremes :: ([a] -> PERMonad ()) -> ([a] -> PERMonad ()) -> InfInteger
                        -> InfInteger -> [a] -> PERMonad ()
manageExtremes fn1 fn2 l u x
    = let range = u - l + 1
        in
            if range == 1 && u < 65536
               then fn1 x
               else if u >= 65536
                    then fn2 x
                    else
                        let Val r = range
                            Val v = l
                        in do encodeConstrainedInt ((fromInteger $ genericLength x - v), fromInteger $ r-1)
                              fn1 x

\end{code}

Clause 38.8 in X680 encoding based on canonical ordering of restricted character string characters

\begin{code}


canEnc b sp [] = tell []
canEnc b sp (f:r)
        = let v = (genericLength . findV f) sp
           in do encodeConstrainedInt (v,b)
                 canEnc b sp r

findV m []  = []
findV m (a:rs)
          = if m == a
                then []
                else a : findV m rs



\end{code}

{-FIXME: Have commented out the decoding stuff for now. -}


\begin{code}

type ElementSetSpecs a = SubtypeConstraint a

fromPER x = decode4 x []

decode4 (BuiltinType t) cl = fromPer3 t cl
decode4 (ConstrainedType t c) cl = decode4 t (c:cl)
decode4 (ReferencedType r t) cl  = decode4 t cl
fromPer3 :: ASNMonadTrans t =>
            ASNBuiltin a -> [ElementSetSpecs a] -> t BG.BitGet a
fromPer3 t@INTEGER cl = decodeInt3 cl
fromPer3 t@(SEQUENCE s) cl = decodeSEQUENCE s
fromPer3 t@(TAGGED _ u) cl = decode4 u cl
fromPer3 t@(SEQUENCEOF s) cl = decodeSequenceOf s cl
fromPer3 t@(BITSTRING _) cl = decodeBitString cl

\end{code}

\section{Decoding Length Determinants}

This function decodes the length determinant as defined in 10.9.
It does not currently cover 10.9.3.4: the determinant being a normally small length.

Note that it assumes that the ASN.1 type makes semantic sense.
For example, if the upper bound of the size constraint ("ub") is 0 and the
lower bound ("lb") is negative, then the result is undefined.


\begin{code}

decodeLengthDeterminant ::
   ASNMonadTrans t =>
   IntegerConstraint -> (Integer -> ASNType a -> t BG.BitGet [b]) -> ASNType a -> t BG.BitGet [b]
decodeLengthDeterminant c f t
   | ub /= maxBound &&
     ub == lb &&
     v <= 64*(2^10) = f v t
   | ub == maxBound = decodeLargeLengthDeterminant3' f t -- FIXME: We don't seem to check if the number
                                                         -- of elements satisfies the lower constraint.
   | v <= 64*(2^10) = do k <- decode4 (ConstrainedType (BuiltinType INTEGER) (rangeConstraint (lb,ub))) []
                         let (Val l) = k
                         f l t
   | otherwise      = decodeLargeLengthDeterminant3' f t
   where
      ub = upper c
      lb = lower c
      (Val v) = ub

      rangeConstraint :: (InfInteger, InfInteger) -> ElementSetSpecs InfInteger
      rangeConstraint =  RootOnly . UnionSet . IC . ATOM . E . V . R

\end{code}

This function decodes the length determinant for unconstrained length or large "ub".
See 10.9.4 and 10.9.3.4 -- 10.9.3.8.4 for further details. Note that we don't currently
cover 10.9.3.4!!! It does so by taking a function which itself takes an iteration count,
an ASN.1 type and returns a (monadic) list of decoded values which may or may not be
values of the ASN.1 type.

\begin{code}

decodeLargeLengthDeterminant3 f t =
   do p <- lift BG.getBit
      if (not p)
         then
            do j <- lift $ BG.getLeftByteString 7
               let l = fromNonNegativeBinaryInteger' 7 j
               f l t
         else
            do q <- lift BG.getBit
               if (not q)
                  then
                     do k <- lift $ BG.getLeftByteString 14
                        let m = fromNonNegativeBinaryInteger' 14 k
                        f m t
                  else
                     do n <- lift $ BG.getLeftByteString 6
                        let fragSize = fromNonNegativeBinaryInteger' 6 n
                        if fragSize <= 0 || fragSize > 4
                           then throwError (DecodeError (fragError ++ show fragSize))
                           else do frag <- f (fragSize * 16 * (2^10)) t
                                   rest <- decodeLargeLengthDeterminant3 f t
                                   return (B.append frag rest)
                        where
                           fragError = "Unable to decode with fragment size of "

decodeLargeLengthDeterminant3' f t =
   do p <- lift BG.getBit
      if (not p)
         then
            do j <- lift $ BG.getLeftByteString 7
               let l = fromNonNegativeBinaryInteger' 7 j
               f l t
         else
            do q <- lift BG.getBit
               if (not q)
                  then
                     do k <- lift $ BG.getLeftByteString 14
                        let m = fromNonNegativeBinaryInteger' 14 k
                        f m t
                  else
                     do n <- lift $ BG.getLeftByteString 6
                        let fragSize = fromNonNegativeBinaryInteger' 6 n
                        if fragSize <= 0 || fragSize > 4
                           then throwError (DecodeError (fragError ++ show fragSize))
                           else do frag <- f (fragSize * 16 * (2^10)) t
                                   rest <- decodeLargeLengthDeterminant3' f t
                                   return (frag ++ rest)
                        where
                           fragError = "Unable to decode with fragment size of "

\end{code}

\section {INTEGER Decoding}

Constrained {\em INTEGER}s are encoded as non-negative binary in
the least number of bits
unless the range is 1 (in which case the answer is the lower and upper bound) --- see Note 2 in Clause 12.

Semi-constrained and unconstrained {\em INTEGER}s are encoded in a list of chunks of
8 bits (octets) as non-negative binary or as two's complement respectively with a
\lq\lq large\rq\rq\ length determinant (as there are no constraints on the length
determinant itself in this particular case).


\begin{code}

decodeInt3 :: ASNMonadTrans t => [ElementSetSpecs InfInteger] -> t BG.BitGet InfInteger
decodeInt3 [] =
   lDecConsInt3 (return bottom) undefined (return bottom)
decodeInt3 cs =
   lDecConsInt3 effRoot extensible effExt
   where
      effCon :: Either String (ExtBS (ConType IntegerConstraint))
      effCon = lSerialEffCons integerConElements top cs
      extensible = eitherExtensible effCon
      effRoot = either (\x -> throwError (ConstraintError "Invalid root"))
                    (return . conType . getRC) effCon
      effExt = either (\x -> throwError (ConstraintError "Invalid extension"))
                    (return . conType . getEC) effCon


lDecConsInt3 :: ASNMonadTrans t =>
                 t BG.BitGet IntegerConstraint -> Bool -> t BG.BitGet IntegerConstraint -> t BG.BitGet InfInteger
lDecConsInt3 mrc isExtensible mec =
   do rc <- mrc
      ec <- mec
      let extensionConstraint    = ec /= bottom
          tc                     = rc `ljoin` ec
          extensionRange         = fromIntegral $ let (Val x) = (upper tc) - (lower tc) + (Val 1) in x -- FIXME: fromIntegral means there's an Int bug lurking here
          rootConstraint         = rc /= bottom
          rootLower              = let Val x = lower rc in x
          rootRange              = fromIntegral $ let (Val x) = (upper rc) - (lower rc) + (Val 1) in x -- FIXME: fromIntegral means there's an Int bug lurking here
          numOfRootBits          = (genericLength . snd . extractValue) $ (encodeConstrainedInt (rootRange - 1, rootRange - 1))
          numOfExtensionBits     = (genericLength . snd . extractValue) $ (encodeConstrainedInt (extensionRange - 1, extensionRange - 1))
          emptyConstraint        = (not rootConstraint) && (not extensionConstraint)
          inRange v x            = (Val v) >= (lower x) &&  (Val v) <= (upper x)
          unconstrained x        = (lower x) == minBound
          semiconstrained x      = (upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          decodeRootConstrained =
             if rootRange <= 1
                then
                   return (Val rootLower)
                else
                   do j <- lift $ BG.getLeftByteString (fromIntegral numOfRootBits)
                      let v = rootLower + (fromNonNegativeBinaryInteger' numOfRootBits j)
                      if v `inRange` rc
                         then
                            return (Val v)
                         else
                            throwError (BoundsError "Value not in root constraint")
          decodeExtensionConstrained =
             do v <- decodeUInt3
                if v `inRange` tc
                   then
                      return (Val v)
                   else
                      throwError (BoundsError "Value not in extension constraint: could be invalid value or unsupported extension")
          foobar
             | emptyConstraint
                  = do x <- decodeUInt3
                       return (Val x)
             | rootConstraint &&
               extensionConstraint
                  = do isExtension <- lift $ BG.getBit
                       if isExtension
                          then
                             decodeExtensionConstrained
                          else
                             decodeRootConstrained
             | rootConstraint &&
               isExtensible
                  = do isExtension <- lift $ BG.getBit
                       if isExtension
                          then
                             throwError (ExtensionError "Extension for constraint not supported")
                          else
                             decodeRootConstrained
             | rootConstraint
                  = decodeRootConstrained
             | extensionConstraint
                  = throwError (ConstraintError "Extension constraint without a root constraint")
             | otherwise
                  = throwError (OtherError "Unexpected error decoding INTEGER")
      foobar

decodeUInt3 :: ASNMonadTrans t => t BG.BitGet Integer
decodeUInt3 =
   do o <- octets
      return (from2sComplement' o)
   where
      chunkBy8 = let compose = (.).(.) in lift `compose` (flip (const (BG.getLeftByteString . fromIntegral . (*8))))
      octets   = decodeLargeLengthDeterminant3 chunkBy8 undefined

\end{code}


\section{SEQUENCE Decoding}

\begin{code}

decodeSEQUENCE s =
   do ps <- lift $ bitMask (l s)
      decodeSEQUENCEAux ps s

l :: Integral n => Sequence a -> n
l EmptySequence = 0
l (AddComponent (MandatoryComponent _) ts) = l ts
l (AddComponent (OptionalComponent  _) ts) = 1 + (l ts)

bitMask n = sequence $ take n $ repeat $ BG.getBit

type BitMap = [Bool]

decodeSEQUENCEAux :: ASNMonadTrans t => BitMap -> Sequence a -> t BG.BitGet a
decodeSEQUENCEAux _ EmptySequence = return Empty -- ignoring the bit map doesn't look right - it's probably an error if it's not empty
decodeSEQUENCEAux bitmap (AddComponent (MandatoryComponent (NamedType _ t)) ts) =
   do x <- decode4 t []
      xs <- decodeSEQUENCEAux bitmap ts
      return (x :*: xs)

\end{code}

\section{SEQUENCE OF Decoding}

\begin{code}

nSequenceOfElements n e = sequence . genericTake n . repeat . flip decode4 e

decodeSequenceOf :: ASNMonadTrans t =>
                    ASNType a -> [ElementSetSpecs [a]] -> t BG.BitGet [a]
decodeSequenceOf t [] = decodeLargeLengthDeterminant3' (flip nSequenceOfElements []) t
decodeSequenceOf t cs = decodeSequenceOfAux t (errorize (effSeqOfCon cs)) (errorize (validSeqOfCon cs))

decodeSequenceOfAux :: ASNMonadTrans t =>
                       ASNType a ->
                       t BG.BitGet (ExtBS (ConType IntegerConstraint)) ->
                       t BG.BitGet (ExtBS (ConType ValidIntegerConstraint)) ->
                       t BG.BitGet [a]
decodeSequenceOfAux t me mv =
   do e <- me
      v <- mv
      let rc = conType . getBSRC $ e
      decodeLengthDeterminant rc (flip nSequenceOfElements []) t

\end{code}

\subsection{BIT STRING --- Clause 15}

{\em BIT STRING}s are encoded with a length determinant but the type
is immaterial hence we use $\bottom$ as the type argument to
{\em decodeLengthDeterminant}; the (function) argument to
decode the individual components merely takes 1 bit at a time.

The above may now be rubbish and the code below could well be
highly inefficient.

\begin{code}

class (MonadError ASNError (t BG.BitGet), MonadTrans t) => ASNMonadTrans t

instance ASNMonadTrans (ErrorT ASNError)

decodeBitString :: ASNMonadTrans t => [ElementSetSpecs BitString] -> t BG.BitGet BitString
decodeBitString constraints =
   do xs <- decodeBitStringAux (errorize (lSerialEffCons lBSConE top constraints))
      return (BitString . concat . (map bitString) $ xs)

decodeBitStringAux :: ASNMonadTrans t => t BG.BitGet (ExtBS (ConType IntegerConstraint)) -> t BG.BitGet [BitString]
decodeBitStringAux mx =
   do x <- mx
      let rc = conType . getBSRC $ x
      decodeLengthDeterminant rc chunkBy1 undefined
      where
         chunkBy1 = let compose = (.).(.) in lift `compose` (flip (const (sequence . return . (liftM BitString) . getBits . fromIntegral)))

getBits 0 =
   return []
getBits n =
   do x <- BG.getBit
      xs <- getBits (n-1)
      return (fromEnum x:xs)

\end{code}

\section{Object Identifier}

\begin{code}

newtype OID = OID {subIds :: [Int]}
   deriving Show

-- type BMonad = ErrorT ASNError BP.BitPut' ()

-- encodeOID :: OID -> BMonad ()
encodeOID x = undefined
   where
      encodeOIDAux []       = undefined -- throwError (BoundsError "encodeOID: an OID must contain at least two object identifier components")
      encodeOIDAux (x:[])   = undefined -- throwError (BoundsError "encodeOID: an OID must contain at least two object identifier components")
      encodeOIDAux (x:y:zs) = if (x >= 0 && x <= 2) && (y >=0 && y <= 39)
                                 then toNonNegativeBinaryInteger 8 ((x*40) + y)
                                 else undefined -- throwError (BoundsError ("encodeOID: invalide oid components: " ++ show x))

\end{code}

\section{Bibliography}

\bibliographystyle{plainnat}

\bibliography{3gpp,ASN1}

\section{Appendix: Tests}

%include TestCTR.lhs

\end{document}
