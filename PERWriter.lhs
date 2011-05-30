\documentclass{report}
%include polycode.fmt

\usepackage{listings}
\usepackage{todonotes}

\lstdefinelanguage{ASN1} {
  keywords={CHOICE, SEQUENCE, BEGIN, END, IMPLICIT, EXPLICIT, INTEGER, DEFINITIONS},
  sensitive=false,
  morecomment=[s]{(--}{--)}
  }

\lstnewenvironment{asn1}[1][]
  {\lstset{language=ASN1,captionpos=b,frame=single,basicstyle=\scriptsize,float,#1}}
  {}

\newcommand{\bottom}{\perp}
\newcommand{\INTEGER}{INTEGER}

\begin{document}

\title{A Formal and Executable Specification of the ASN.1 Packed Encoding Rules}

\author{D. J. Russell \and D. J. Steinitz}

\maketitle

\tableofcontents

\listoftodos

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

\section{Conventions}

In order make the code more intelligible without using overlong identifiers, we adopt
the following conventions:

\begin{itemize}

\item
All encoding functions begin with ``e''.

\item
All decoding functions begin with ``d''.

\item
A part of an identifier ``Cons'' is short form for ``Constrained''.

\item
A part of an identifier ``Uncons'' is short form for ``Unconstrained''.

\end{itemize}

\section{UNALIGNED CANONICAL-PER}

%if False

\begin{code}

{-# LANGUAGE MultiParamTypeClasses, GADTs, TypeOperators, EmptyDataDecls, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving, ScopedTypeVariables, PatternGuards, DoRec #-}

{-# OPTIONS_GHC -fwarn-unused-binds -fwarn-unused-imports #-}

{-  -fwarn-incomplete-patterns -fwarn-unused-matches #-}

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

module PERWriter where

import ASNTYPE
import LatticeMod
import ConstraintGeneration
import Language.ASN1.PER.Integer
   ( fromNonNegativeBinaryInteger'
   , from2sComplement'
   )
import Data.List as L hiding (groupBy)
import Data.Char
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Writer

{- FIXME: added IntegerAux and Word for encodeNonNegBinaryIntInOctets and h' -}
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.BitPut as BP
import qualified Data.Binary.BitBuilder as BB
import qualified Language.ASN1.PER.Integer as I
import Data.Int
import Control.Applicative

import Debug.Trace

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
The input is a referenced type value. The reference is L.dropped
and {\em encode} is recursively called on the value.
\item
The input is a constrained type value. The constraint is added to the list of constraints and
the function is called again on the type being constrained. This recursion will continue
until we reach a non-constrained type. The associated list of constraints will then include all
of the seraily applied constraints.
\end{itemize}

The function {\em encode} returns a value of type {\em PERMonad ()}. This is a type that can deal with
\begin{itemize}
\item
the output of an encoding; and
\item
error handling
\end{itemize}

In Haskell when we want to represent and manage computations such as writing output or
handling errors we typcially use a {\em monadic} type. Haskell provides several commonly used
monadic types such as
\begin{itemize}
\item
the {\em Maybe} type for dealing with failure;
\item
the {\em IO} type for interaction with the user; and the
\item
list type for dealing with nondeterminism.
\end{itemize}

Each of these types (and other types) are members of the Haskell type class {\em Monad} which captures
the behavioural requirements of a monad as a collection of operations supported by each of its member types.
Haskell also provides monad transformers which combine existing monads to produce new monads
with the characteristics of the component monads. Two such monad transformers are {\em ErrorT}
which adds error handling capabilities to a monad, and {\em WriterT} which adds support for producing a
stream of values.

Thus the type {\em PERMonad} can produce a stream of values of type {\em BitStream} (the encoding type),
and can handle errors of the type {\em ASNError}. This error type enables the categorisation of the various types of
error.

\begin{code}


type PERMonad a = WriterT BB.BitBuilder (ErrorT ASNError Identity) a

type UnPERMonad a = ErrorT ASNError BG.BitGet a

data ASNError =
     ConstraintError String
   | BoundsError     String
   | DecodeError     String
   | ExtensionError  String
   | OtherError      String
      deriving Show

instance Error ASNError where
   noMsg = OtherError "The impossible happened"


encode :: ASNType a -> SerialSubtypeConstraints a -> a -> PERMonad ()
encode (BuiltinType t) cl v       = toPER t v cl
encode (ReferencedType r t) cl v  = encode t cl v
encode (ConstrainedType t c) cl v = encode t (c:cl) v

decode :: ASNType a -> [ElementSetSpecs a] -> UnPERMonad a
decode (BuiltinType t) cl       = fromPER t cl
decode (ConstrainedType t c) cl = decode t (c:cl)
decode (ReferencedType r t) cl  = decode t cl

runDecode :: ASNType a -> B.ByteString -> a
runDecode t bs = case BG.runBitGet bs (runErrorT (decode t [])) of
                   Left s  -> error s
                   Right x -> case x of
                                Left e  -> error $ show e
                                Right y -> y

-- FIXME: B.pack . BL.unpack doesn't look right but I don't want to think about it now
runEncode :: ASNType a -> a -> B.ByteString
runEncode t v = case extractValue $ encode t [] v of
                  Left e         -> error $ show e
                  Right ((), bb) -> B.pack $ BL.unpack $ BB.toLazyByteString bb

\end{code}

The function {\em toPER} L.takes an {\em ASNBuiltin} type, a value of the same builtin type and
a list of subtype constraints, and encodes the value using PER. The first input is essential
in determining the encoding algorithm to use. That is, it is a pointer to the appropriate
encoding function for the value. For example, if the type is {\em INTEGER} then {\em
eInteger} is called, and if it is a {\em CHOICE} type then {\em encodeChoice} is used.

\begin{code}

toPER :: ASNBuiltin a -> a -> SerialSubtypeConstraints a -> PERMonad ()
toPER NULL _ _             = tell BB.empty
toPER INTEGER x cl         = eInteger cl x
toPER VISIBLESTRING x cl   = encodeKMS cl x
toPER PRINTABLESTRING x cl = encodeKMS cl x
toPER NUMERICSTRING x cl   = encodeKMS cl x
toPER IA5STRING x cl       = encodeKMS cl x
toPER BMPSTRING x cl       = encodeKMS cl x
toPER UNIVERSALSTRING x cl = encodeKMS cl x
toPER BOOLEAN x cl         = encodeBool cl x
toPER (ENUMERATED e) x cl  = encodeEnum e cl x -- no PER-Visible constraints
toPER (BITSTRING nbs) x cl = encodeBitstring nbs cl x
toPER (OCTETSTRING) x cl   = encodeOctetstring cl x
toPER (SEQUENCE s) x cl    = encodeSequence s x -- no PER-Visible constraints
toPER (SEQUENCEOF s) x cl  = encodeSequenceOf cl s x
toPER (SET s) x cl         = encodeSet s x -- no PER-Visible constraints
toPER (CHOICE c) x cl      = encodeChoice c x -- no PER-visible constraints
toPER (SETOF s) x cl       = encodeSetOf cl s x -- no PER-visible constraints
toPER (TAGGED tag t) x cl  = encode t cl x

fromPER :: ASNBuiltin a -> [ElementSetSpecs a] -> UnPERMonad a
fromPER t@INTEGER cl = dInteger cl
-- FIXME: Why are we ignoring the constraints?
fromPER t@(SEQUENCE s) cl = dSequence s

\end{code}

\section{COMPLETE ENCODING}

{\em completeEncode} implements X.691 10.1. That is, it adds a single octet with all
bits set to 0 to an empty encoding and leaves a non-empty encoding unchanged.

\begin{code}
completeEncode :: PERMonad () -> PERMonad ()
completeEncode m
    =  {- X691REF: 10.1 -}
       let bs = extractValue m
       in case bs of
            {- X691REF: 10.1.3 with empty bit string -}
            (Right (_,empty)) -> tell $ BB.fromBits 8 (0x00::Int)
            {- X691REF: 10.1.3 with non-empty bit string -}
            x -> m
\end{code}

\section{ENCODING AN OPEN TYPE FIELD}



{\em encodeOpen} encodes an open type value. It uses the function {\em extractValue} which L.takes a {\em
PERMonad ()} value and returns either
\begin{itemize}
\item
an error value; or
\item
a pair whose second element is the encoding value.
\end{itemize}

It also uses the function {\em encodeCase} which takes the extracted value and a function
which acts on the bitstream included in it. If the extracted value indicates an error then the
error is simply passed on. Othwerwise, the function is applied to the bitstream.


\begin{code}
encodeOpen :: ASNType a -> a -> PERMonad ()
encodeOpen t v
{- X691REF: 10.2.1 -}   = let x = extractValue (completeEncode $ encode t [] v)
{- X691REF: 10.2.2 -}     in  encodeCase x encodeOctetsWithLength


getByteString (Right (a,b)) = BB.toLazyByteString b
getByteString x = error "Oops!"

extractValue ::  PERMonad () -> Either ASNError ((), BB.BitBuilder)
extractValue  = runIdentity . runErrorT . runWriterT

encodeCase :: Either ASNError ((), BB.BitBuilder) -> (BL.ByteString -> PERMonad ()) -> PERMonad ()
encodeCase (Left s) _ = throwError s
encodeCase x f = (f . getByteString) x
\end{code}

\section{ENCODING A LENGTH DETERMINANT}

Several PER encodings require the encoding of a length determinant. If the item to be encoded
is very large or, in the case of integer encoding, the number of bits produced by the encoding
is very large, then some fragmenting may be required in which L.length and value encodings are
interleaved.

{\em encodeWithLength} is a higher order function which takes a constraint, an encoding function
and a list of values (could be bits, octets or any ASN.1 type). The approach to encoding depends on whether
the constraint imposes an upper bound which is less than 64K. If it does then no interleaving is required and
the value is encoded with a L.length prefix if the upper bound differs from the lower bound, and
with no L.length encoding otherwise.

If the upper bound is at least 64K then {\em encodeUnconstrainedL.length} is called. The items are grouped
first in 16k batches, and then in batches of 4. The input encoding function is then supplied as
an input to the function {\em encodeUnconstrainedL.length} which manages the interleaving of
L.length and value encodings -- it encodes the L.length and values of
each batch and concatenates their resulting bitstreams together.
Note the values are encoded using the input function.

Note that {\em encodeWithL.length} is not used to encode {\bf normally small L.length}
determinants (see X691: 10.9.3.4} which are only used with the bitmap that prefixes the
extension addition values of a set or sequence type.

\begin{code}

encodeWithLength :: IntegerConstraint -> (t -> PERMonad ()) -> [t] -> PERMonad ()
encodeWithLength ic fun ls
    = if constrained ic && ub < k64
          then {- X691REF: 10.9.4.1 -}
                if lb == ub
                    then
                         do tell BB.empty
                            mapM_ fun ls
                    else
                        do toNonNegBinaryInteger (fromInteger (L.genericLength ls) - lb) (ub - lb)
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
function and the list of values to be encoded. If the L.length of the input value is less than
16K then the L.length is encoded followed by the value. Otherwise the auxiliary function {\em
encodeUnconstrainedLengthAux} is called. This function manages the fragmenting of the input
value into blocks of at most four 16K blocks. These are each encoded -- their block L.length
followed by the encoding of the block of values -- and if the block contains four 16k
blocks the process is repeated with the next block of 16K values.

{\em lengthLessThan16K} encodes the length of a list of less than 16K values and {\em blockLen}
encodes the L.length of a block (1 to 4).

\begin{code}

encodeUnconstrainedLength :: (b -> PERMonad ()) -> [b] -> PERMonad ()
encodeUnconstrainedLength encFun []
    = lengthLessThan16K 0 {- FIXME: Is this only the case when there is at least 16k values? 10.9.3.8.3
                                    See definition of encodeUnconstrainedLengthAux -}
encodeUnconstrainedLength encFun xs
    | l < k16
    {- X691REF: 10.9.3.6 AND 10.9.3.7 -}
        = do lengthLessThan16K l
             mapM_ encFun xs
    | otherwise
    {- X691REF: 10.9.3.8 -}
       = encodeUnconstrainedLengthAux encFun xs
         where l = L.genericLength xs

encodeUnconstrainedLengthAux :: (b -> PERMonad ()) -> [b] -> PERMonad ()
encodeUnconstrainedLengthAux encFun [] = throwError (OtherError "Nothing to encode")
encodeUnconstrainedLengthAux encFun xs
    | l == 4 && last16 == k16
        = do blockLen 4 63
             mapM_ (mapM_ encFun) x
             encodeUnconstrainedLength encFun (L.drop (64*(2^10)) xs)
    | otherwise
        = if last16 == k16
             then do blockLen l 63
                     mapM_ (mapM_ encFun) x
                     {- X691REF: Note associated with 10.9.3.8.3 -}
                     lengthLessThan16K 0
             else do blockLen (l-1) 63
                     mapM_ (mapM_ encFun) (init x)
                     lengthLessThan16K ((L.genericLength.last) x)
                     mapM_ encFun (last x)
    where
        (x:_)      = (groupBy 4 . groupBy (16*(2^10))) $ xs
        l          = L.genericLength x
        last16     = (L.genericLength . last) x

k16 :: InfInteger
k16    = 16*(2^10)

groupBy :: Int -> [t] -> [[t]]
groupBy n =
   L.unfoldr k
      where
         k [] = Nothing
         k p = Just (L.splitAt n p)

lengthLessThan16K :: InfInteger -> PERMonad ()
lengthLessThan16K n
   | n <= 127
     {- X691REF: 10.9.3.6 -}
        = do zeroBit
             toNonNegBinaryInteger n 127
   | n < k16
     {- X691REF: 10.9.3.7 -}
        = do oneBit
             zeroBit
             toNonNegBinaryInteger n (k16 - 1)
   | otherwise
        = throwError (BoundsError "Length is out of range.")

blockLen :: InfInteger -> InfInteger -> PERMonad ()
blockLen x y
    = do oneBit
         oneBit
         toNonNegBinaryInteger x y


noBit :: PERMonad ()
noBit = tell BB.empty
zeroBit :: (MonadWriter BB.BitBuilder m) => m ()
zeroBit = tell $ BB.singleton False
oneBit :: PERMonad ()
oneBit  = tell $ BB.singleton True
\end{code}


\begin{code}

-- FIXME: We should write this as an unfold rather than use primitive recursion
decodeLargeLengthDeterminant :: (Integer -> t -> UnPERMonad B.ByteString) -> t -> UnPERMonad B.ByteString
decodeLargeLengthDeterminant f t =
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
                                   rest <- decodeLargeLengthDeterminant f t
                                   return (B.append frag rest)
                        where
                           fragError = "Unable to decode with fragment size of "


\end{code}

\section{ENCODING THE BOOLEAN TYPE}

\begin{code}

{- FIXME: I think this is as good as it's worth doing for now -}
{- Clearly we want to just say e.g. tell 1                    -}
{- Or do we. It is meant to return a bit-field value and not just a bit -}
{- So the following whould be fine. -}
encodeBool :: [SubtypeConstraint Bool] -> Bool -> PERMonad ()
encodeBool t x = tell $ BB.singleton x


\end{code}

\section{Stuff Used All Over but Which Needs Fixing}

\todo{We normally stay in the monad and propogate any errors --- so make eitherExtensible redundant}

\begin{code}
eitherExtensible (Right v) = isExtensible v
eitherExtensible _ = False

eitherExtensible' :: MonadError ASNError m => Either String a -> m a
eitherExtensible' (Right v) = return v
eitherExtensible' (Left s)  = throwError $ ConstraintError s

evaluateConstraint' :: (Lattice a, Constraint a, Eq a, MonadError ASNError m)  =>
                       (Element InfInteger -> Bool -> Either String (ExtensibleConstraint a)) ->
                       Either String (ExtensibleConstraint a) ->
                       [SubtypeConstraint InfInteger] -> m (ExtensibleConstraint a)
evaluateConstraint' x y z = eitherExtensible' $ evaluateConstraint x y z
\end{code}

{\em toNonNegBinaryInteger} encodes an integer in the minimum
number of bits required for the range specified by the constraint
(assuming the range is at least 2). The value encoded is the offset from the lower bound of
the constraint.

\begin{code}
toNonNegBinaryInteger :: InfInteger -> InfInteger -> PERMonad ()
toNonNegBinaryInteger (Val val) (Val range) = toNonNegBinaryIntegerAux val range
   where
      toNonNegBinaryIntegerAux :: Integer -> Integer -> PERMonad ()
      toNonNegBinaryIntegerAux _ 0 = tell BB.empty
      toNonNegBinaryIntegerAux 0 w
          = toNonNegBinaryIntegerAux 0 (w `div` 2) >> zeroBit
      toNonNegBinaryIntegerAux n w
          = toNonNegBinaryIntegerAux (n `div` 2) (w `div` 2) >> (tell . BB.fromBits 1) n

toNonNegBinaryInteger x y = throwError . OtherError $ "Cannot encode: " ++ show x ++ " in " ++ show y
\end{code}

\begin{code}
encodeNonNegBinaryIntInOctets :: InfInteger -> PERMonad ()
encodeNonNegBinaryIntInOctets (Val x) = h 8 x where
   h p 0 = tell $ L.foldr BB.append BB.empty (L.replicate p (BB.singleton False))
   h 0 n = h 7       (n `div` 2) >> (tell . BB.fromBits 1) n
   h p n = h (p - 1) (n `div` 2) >> (tell . BB.fromBits 1) n
encodeNonNegBinaryIntInOctets y = throwError . OtherError $ "Cannot encode: " ++ show y
\end{code}

{\em encodeOctetsWithLength} encodes a collection of octets with
unconstrained length. {\em encodeBitsWithLength} does the same except
for a collection of bits.

\begin{code}
encodeOctetsWithLength :: BL.ByteString -> PERMonad ()
encodeOctetsWithLength bs
    = encodeUnconstrainedLength (tell . BB.fromBits 8) $ BL.unpack bs


encodeBitsWithLength :: BitStream -> PERMonad ()
encodeBitsWithLength = encodeUnconstrainedLength (tell . BB.fromBits 1)
\end{code}

\begin{code}
minBits :: Integer -> Integer
minBits n = f n 0
   where
      f 0 a = a
      f n a = f (n `div` 2) (a+1)
\end{code}

\todo[owner={Dan}]{Why do we have SubtypeConstraint? Isn't the right terminology ElementSetSpecs?}

\begin{code}
type ElementSetSpecs a = SubtypeConstraint a
\end{code}

\section{ENCODING THE INTEGER TYPE}
\label{intEnc}

\todo{This seems out of place}
Note that if a constraint is serially applied to an extensible constraint
then any extension additions of the extensible constraint are discarded (see X.680 Annex
G.4.2.3). That is, the extensibility and extension additions of the effective constraint are
determined only by the last constraint.

We first define some helper functions to assist with checking whether a constraint is empty
and, for \INTEGER constraints whether a value is in the range specified by the constraints.

\begin{code}
isEmptyConstraint, isNonEmptyConstraint :: (Eq t, Lattice t) => t -> Bool
isEmptyConstraint    x  = x == bottom
isNonEmptyConstraint x  = x /= bottom
\end{code}

\begin{code}
inRangeSingle :: InfInteger -> IntegerConstraint -> Bool
inRangeSingle n c =  n >= (lower c) && n <= (upper c)

inRange :: InfInteger -> ValidIntegerConstraint -> Bool
inRange n vc | Valid cs <- vc = or . map (inRangeSingle n) $ cs
\end{code}

We split the encoding of an \INTEGER\ into two cases depending on whether
there are any constraints.

\begin{code}
eInteger :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
eInteger [] v = eUnconsInteger v
eInteger cs v = eConsInteger cs v
\end{code}

We encode an unconstrained \INTEGER\ value as a 2's-complement-binary-integer
in a minimum number of octets prefixed by an explicit
length.

\begin{code}
eUnconsInteger :: InfInteger -> PERMonad ()
eUnconsInteger (Val x) = {- X691REF: 12.2.4 -}
                         encodeOctetsWithLength .
                         BP.runBitPut .
                         I.to2sComplementM  $ x
eUnconsInteger v       = throwError (BoundsError ("Cannot encode " ++ show v))
\end{code}

We split the encoding of a constrained \INTEGER into two cases depending
on whether the effective constraint is extensible.

\begin{code}
eConsInteger :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
eConsInteger cs v    = do
      actualCon    <- evaluateConstraint' pvIntegerElements top cs
      effectiveCon <- evaluateConstraint' pvIntegerElements top cs
      if isExtensible effectiveCon
        then {- X691REF: 12.1 -} eExtConsInteger    actualCon effectiveCon v
        else {- X691REF: 12.2 -} encodeNonExtConsInt actualCon effectiveCon v
\end{code}

If the constraints are empty or the value to be encoded is not valid value
of the constrained type then we throw an error otherwise we follow the encoding
rules in Clause 12.

\begin{code}
encodeNonExtConsInt :: ExtensibleConstraint ValidIntegerConstraint ->
                       ExtensibleConstraint IntegerConstraint ->
                       InfInteger ->
                       PERMonad ()
encodeNonExtConsInt actualCon effectiveCon n
   | isEmptyConstraint effRootCon =
        throwError (ConstraintError "Empty constraint")
   | isNonEmptyConstraint effRootCon && inRange n validRootCon =
        eRootConsInteger (constraintType effRootCon) n rootLower rootUpper
   | otherwise =
        throwError (BoundsError "Value out of range")

   where
      effRootCon   = getRootConstraint effectiveCon
      validRootCon = getRootConstraint actualCon
      rootLower    = lower effRootCon
      rootUpper    = upper effRootCon

eExtConsInteger :: ExtensibleConstraint ValidIntegerConstraint ->
                   ExtensibleConstraint IntegerConstraint ->
                   InfInteger ->
                   PERMonad ()
eExtConsInteger actualCon effectiveCon n
   | isEmptyConstraint effRootCon && isEmptyConstraint effExtCon =
       throwError (ConstraintError "Empty constraint")
   | isNonEmptyConstraint effRootCon && inRange n validRootCon = do
       zeroBit
       eRootConsInteger (constraintType effRootCon) n rootLower rootUpper
   | isNonEmptyConstraint effExtCon && inRange n validExtCon = do
        {- X691REF: 12.1 -}
        oneBit
        eUnconsInteger n
   | otherwise =
        throwError (BoundsError "Value out of range")

   where
      effRootCon   = getRootConstraint effectiveCon
      validRootCon = getRootConstraint actualCon
      effExtCon    = getExtConstraint effectiveCon
      validExtCon  = getExtConstraint actualCon
      rootLower    = lower effRootCon
      rootUpper    = upper effRootCon

eRootConsInteger :: IntegerConstraintType ->
                    InfInteger ->
                    InfInteger ->
                    InfInteger ->
                    PERMonad ()
eRootConsInteger UnConstrained   n _l _u = {- X691REF: 12.2.4 -}
                                           eUnconsInteger n
eRootConsInteger SemiConstrained n  l _u = {- X691REF: 12.2.3 -}
                                           eSemiConsInteger n l
eRootConsInteger Constrained     n  l  u = {- X691REF: 12.2.2 -}
                                           toNonNegBinaryInteger (n - l) (u - l)
\end{code}

We encode a semi-constrained integer as a non-negative-binary-integer of the difference between the value and the
lower bound in the mininum number of octets prefixed by the length of the
octets.

\begin{code}
eSemiConsInteger :: InfInteger -> InfInteger -> PERMonad ()
eSemiConsInteger x@(Val _) lb@(Val _) =  encodeNonNegBinaryIntInOctets $ x - lb
eSemiConsInteger x (Val _)
    = throwError . BoundsError $ "Cannot encode " ++ show x ++ "."
eSemiConsInteger _ _
    = throwError . ConstraintError $ "No lower bound."
\end{code}

We split the decoding of an \INTEGER\ into two cases depending on whether
there are any constraints.

\begin{code}
dInteger :: [ElementSetSpecs InfInteger] -> UnPERMonad InfInteger
dInteger [] = dConsInteger top undefined top
dInteger cs = do
   effectiveCon <- evaluateConstraint' pvIntegerElements top cs
   let effRoot = getRootConstraint effectiveCon
       effExt  = getExtConstraint effectiveCon
   dConsInteger effRoot (isExtensible effectiveCon) effExt
\end{code}

To decode an unconstrained \INTEGER\ , we parameterise
{\em decodeLargeLengthDeterminant} by a function which ignores
the second parameter chunking up the bits being read into
groups of 8.

\begin{code}
dUnconInteger :: UnPERMonad Integer
dUnconInteger =
   from2sComplement' <$> decodeLargeLengthDeterminant chunkBy8 undefined
   where
      chunkBy8 :: Integer -> a -> UnPERMonad B.ByteString
      chunkBy8 n _ =
        lift $ (flip (const (BG.getLeftByteString . fromIntegral . (*8)))) n undefined
\end{code}

\begin{code}
dConsInteger :: IntegerConstraint ->
                Bool ->
                IntegerConstraint ->
                UnPERMonad InfInteger
dConsInteger rc isExtensible ec =
   do let isRootConstraint       = rc /= top
          isExtensionConstraint  = ec /= top
          isEmptyConstraint      = (not isRootConstraint) && (not isExtensionConstraint)
          tc                     = rc `ljoin` ec
          rootLower              = let Val x = lower rc in x
          rootRange              = let (Val x) = (upper rc) - (lower rc) + (Val 1) in x
          numOfRootBits          = minBits rootRange

          dConsIntegerAux
             | isEmptyConstraint
                  = do {- X691REF: 12.2.4 -}
                       x <- dUnconInteger
                       return (Val x)
             | isRootConstraint &&
               isExtensionConstraint
                  = do {- X691REF: 12.1 -}
                       isExtension <- lift $ BG.getBit
                       if isExtension
                          then
                             dExtConsInteger
                          else
                             dRootConsInteger
             | isRootConstraint &&
               isExtensible
                  = do {- X691REF: 12.1 -}
                       isExtension <- lift $ BG.getBit
                       if isExtension
                          then
                             throwError (ExtensionError "Extension for constraint not supported")
                          else
                             dRootConsInteger
             | isRootConstraint
                  = dRootConsInteger
             | isExtensionConstraint
                  = throwError (ConstraintError "Extension constraint without a root constraint")
             | otherwise
                  = throwError (OtherError "Unexpected error decoding INTEGER")

          dExtConsInteger =
             do v <- dUnconInteger
                if (Val v) `inRangeSingle` tc
                   then
                      return (Val v)
                   else
                      throwError (BoundsError "Value not in extension constraint: could be invalid value or unsupported extension")

          dRootConsInteger =
             if rootRange <= 1
                then
                   {- X691REF: 12.2.1 -}
                   return (Val rootLower)
                else
                   do {- X691REF: 12.2.2 and 12.2.3 -}
                      j <- lift $ BG.getLeftByteString (fromIntegral numOfRootBits)
                      let v = rootLower + (fromNonNegativeBinaryInteger' numOfRootBits j)
                      if (Val v) `inRangeSingle` rc
                         then
                            return (Val v)
                         else
                            throwError (BoundsError "Value not in root constraint")

      dConsIntegerAux
\end{code}


\section{ENCODING THE ENUMERATED TYPE}

{\em encodeEnum} L.takes the defined enumeration type, the (possibly empty) list of serially applied constraints
and the enumeration value. Since there are no
PER-visible constraints, the constraints are used only to test the validity of the input enumeration.
If the value is valid then the function {\em assignIndex} is applied to the enumeration type.
This returns a pair
whose first element indicates if an extension marker is present in the type, and whose second
element is a list of indices assigned to the enumeration values. The index assigned to each
enumeration value is determined by the enumeration number associated with each enumeration.
These are either assigned explicitly when the enumeration is defined, or implicitly by the
function {\em assignNumber}. {\tt assignIndex}, {\tt assignNumber} and their auxilliary functions
are defined in the module {\tt ASNType} with the {\tt Enumerate} type. This is because they are
used both in the encoding of an enumerate value, and in the generation of a constraint used to test
the validity of an enumeration value.

{\em encodeEnum} calls the auxiliary function {\em encodeEnumAux} which manages the various
encoding cases. Its second input is the number of enumeration root values which is required
since a root enumeration will be encoded as a constrained integer.

Note that {\em encodeEnum} does not have a constraint input since there are no PER-visible
enumerated type constraints.

\begin{code}

encodeEnum :: Enumerate -> SerialSubtypeConstraints Enumerate -> Enumerate -> PERMonad ()
encodeEnum e cs x @ (AddEnumeration ei EmptyEnumeration)
    =  let (extensible,inds) = assignIndex e {- X691REF: 13.1 -}
           no = L.genericLength inds
           (b,p) = validEnum e ei 0
           n = getName ei
       in
                if b && (not . L.null) cs
           then
               let Just pos = p
                   i = inds !! pos
                   vc = evaluateConstraint (enumeratedElements e) (Right (ExtensibleConstraint top top False)) cs
                                in if withinConstraint i vc
                                then
                                  encodeEnumAux extensible no inds e n
                                          else
                                                throwError (BoundsError "Invalid enumeration")
                     else
                                if b
                                     then
                                        encodeEnumAux extensible no inds e n
                                     else throwError (OtherError "Invalid enumeration")

withinConstraint i (Right (ExtensibleConstraint (EnumeratedConstraint ls) _ _))
                                 = elem i ls
withinConstraint i _
                                 = False
\end{code}

{\em encodeEnumAux} is a recursive function which recurses through the enumeration value until
it reaches the enumeration. If no extension marker is present then the enumeration is
encoded using {\em toNonNegBinaryInteger}. If the marker is present and the enumeration is
in the extension root then it is encoded as above but prefixed by 0.

If the enumeration is not in the extension root then the encoding is passed to a second
auxiliary function {\em encodeEnumExtAux}. This is also a recursive function which encodes an
enumeration as a normally small non-negative integer using {\em encodeNSNNInt} prefixed by a
1.

\begin{code}

encodeEnumAux :: Bool -> Integer -> [Integer] -> Enumerate -> Name
                 -> PERMonad ()
encodeEnumAux extensible no (f:r) (AddEnumeration ei es) n
    | getName ei == n
        = if not extensible
            then    {- X691REF: 13.2 -}
                    toNonNegBinaryInteger (fromInteger f) (fromInteger $ no - 1)
            else do {- X691REF: 13.2 -}
                    zeroBit
                    toNonNegBinaryInteger (fromInteger f) (fromInteger $ no - 1)
    | otherwise
        = encodeEnumAux extensible no r es n
encodeEnumAux b no inds (EnumerationExtensionMarker   ex) x
    = let el = noEnums ex
      in encodeEnumExtAux 0 el ex x
encodeEnumAux _ _ _ _ _ = throwError (OtherError "No enumerated value!")

encodeEnumExtAux :: Integer -> Integer -> Enumerate -> Name
                    -> PERMonad ()
encodeEnumExtAux i l (AddEnumeration  ei es) n
    | getName ei == n
        = do    {- X691REF: 13.3 -}
                oneBit
                encodeNSNNInt i 0
    | otherwise
        = encodeEnumExtAux (i+1) l es n
encodeEnumExtAux i l _ _ = throwError (OtherError "No enumerated extension value!")


getName :: EnumerationItem -> Name
getName (Identifier n) = n
getName (NamedNumber n _) = n

\end{code}

{\em encodeNSNNInt} encodes a normally small non-negative integer.
\begin{code}

encodeNSNNInt :: Integer -> Integer -> PERMonad ()
encodeNSNNInt n lb
    = if n <= 63
        then do {- X691REF: 10.6.1 -}
                zeroBit
                toNonNegBinaryInteger (fromInteger n) (fromInteger 63)
        else do {- X691REF: 10.6.2 -}
                oneBit
                eSemiConsInteger (fromInteger n) (fromInteger lb)


\end{code}

\section{ENCODING THE REAL TYPE} {- FIXME: To do? -}

\section{ENCODING THE BIT STRING TYPE}


{\em encodeBitstring} L.takes the usual two inputs -- the list of serially applied constraints
and the value to be encoded -- and an additional input, the named bits of type {\em
NamedBits}. If the constraint list is empty the function {\em encodeUnconstrainedBitstring} is
called. Otherwise, {\em encodeBitstringWithConstraint} is called. Note that there are two ways
in which a BITSTRING type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible. This is determined when generating the effective constraint
for a type using the function {\em lSerialeffectiveCon} defined in the module {\em
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

{\em encodeUnconstrainedBitstring} encodes the bitstring with a L.length determinant using {\em
encodeBitsWithL.length}. If there are any named bits then trailing 0 bits are removed in advance
of encoding.

\begin{code}
encodeUnconstrainedBitstring :: NamedBits -> BitString -> PERMonad ()
encodeUnconstrainedBitstring namedBits (BitString [])
    = return () -- tell []
encodeUnconstrainedBitstring namedBits (BitString bs)
    = let rem0 = if (not.L.null) namedBits
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
extensible. If it is extensible then {\em encodeExtConsBitstring} is called. They both L.take the
effective constraint and actual constraint associated with the type as input.

\begin{code}

encodeBitstringWithConstraint :: NamedBits -> [SubtypeConstraint BitString] -> BitString
                                 -> PERMonad ()
encodeBitstringWithConstraint namedBits cs v
    = if (not extensible)
        then {- X691REF: 15.7 -}
             encodeNonExtConsBitstring namedBits actualCon effectiveCon v
        else {- X691REF: 15.6 -}
             encodeExtConsBitstring namedBits actualCon effectiveCon v
      where
          effectiveCon :: Either String (ExtensibleConstraint IntegerConstraint)
          effectiveCon = evaluateConstraint  pvBitStringElements top cs
          actualCon :: Either String (ExtensibleConstraint ValidIntegerConstraint)
          actualCon = evaluateConstraint  pvBitStringElements top cs
          extensible = eitherExtensible effectiveCon

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

encodeNonExtConsBitstring :: NamedBits -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> BitString
                -> PERMonad ()
encodeNonExtConsBitstring nbs _ (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf) _ _))
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
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                vrc = getRootConstraint ok

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

encodeExtConsBitstring :: NamedBits -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> BitString
                -> PERMonad()
encodeExtConsBitstring nbs _
    (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf)
                  (IntegerConstraint NegInf PosInf) _)) (BitString vs)
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
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                ec = getExtConstraint vsc
                vrc = getRootConstraint ok
                vec = getExtConstraint ok

\end{code}

{\em encodeConstrainedBitstring} L.takes a prefix bit as the first
input and has two list-pattern based cases. The first case has an empty list
as its second argument indicating that there are no named bits. The second case uses the
pattern {\em (b:rs)} to indicate that there is at least one named bit.

Note that X.691 15.8 states that if a bitstring is constrained to be of zero L.length then
it shall not be encoded. It is not clear whether this means that a bitstring with no L.length is
not encoded, or if any bitstring associated with a bitstring type with a zero-L.length
constraint is not encoded. We have implemented it using the former case. That is, the
bitstring must satisfy the constraint (up to the removal of trailing 0 bits as described in
X.691 15.3).
\begin{code}

type PrefixBit = BitStream

encodeConstrainedBitstring :: PrefixBit -> NamedBits -> InfInteger -> InfInteger
                                -> ValidIntegerConstraint -> BitStream -> PERMonad ()
encodeConstrainedBitstring pb bs l u (Valid vrc) xs
     | L.null bs && not (inSizeRange xs vrc)
                    = throwError (BoundsError "Size out of range")
     | (not . L.null) bs && lxs > u && (L.take (fromInteger n) . L.reverse) xs /= L.take (fromInteger n) zeros
                    = throwError (OtherError "Last value is not 0")
     | L.null bs && inSizeRange xs vrc
            = encodeConBS pb l u xs
     | otherwise
     {- X691REF: 15.3 -}
                = let nxs = namedBitsEdit l u xs
                            in
                                encodeConBS pb l u nxs
        where
                 lxs = L.genericLength xs
                 Val n = (lxs - u)


\end{code}

{\em inSizeRange} is a predicate that tests whether a value satisfies a size constraint. The
L.length of the value is tested against the actual constraint -- possibly a non-contiguous set
of values -- and not against the effective constraint.

{\em namedBitsEdit} applies the necessary pruning of or appending of 0s to a bitstring to
produce a minimal size value that satisfies the constraint associated with the type. This is
only applied when the BIT STRING type has associated named bits.

\begin{code}

inSizeRange :: [b] -> [IntegerConstraint] -> Bool
inSizeRange _  [] = False
inSizeRange p qs = inSizeRangeAux qs
   where
      l = L.genericLength p
      inSizeRangeAux (x:rs) =
         l >= (lower x) && l <= (upper x) || inSizeRangeAux rs
      inSizeRangeAux [] = False


namedBitsEdit :: InfInteger -> InfInteger -> BitStream -> BitStream
namedBitsEdit l u xs
    = let lxs = L.genericLength xs
      in if lxs < l
        then add0s (l-lxs) xs
        else
            if lxs > u
             then rem0s (lxs-u) l xs
             else rem0s' l xs

add0s :: InfInteger -> BitStream -> BitStream
add0s (Val n) xs =  xs ++ L.take (fromInteger n) zeros

zeros :: BitStream
zeros = [0,0..]

putBitstream (a:xs)
    = (tell . BB.fromBits 1) a >> putBitstream xs
putBitstream []
    = noBit
\end{code}

\todo{Should we use higher order functions here rather
than recursion?}

\begin{code}
rem0s :: InfInteger -> InfInteger -> BitStream -> BitStream
rem0s (Val 0) l xs = rem0s' l xs
rem0s (Val n) l xs = rem0s (Val (n - 1)) l (init xs)

rem0s' :: InfInteger -> BitStream -> BitStream
rem0s' l xs
    = if L.genericLength xs > l && last xs == 0
        then rem0s' l (init xs)
        else xs
\end{code}

{\em encodeConBS}  applies one of X.691 15.8-15.11.

Note that in the last case of {\em encodeConBS} the lower bound of the constraint is ignored.
This is because the lower bound does not affect these L.length encodings (X.691 10.9.3.5 Note).

\begin{code}

encodeConBS :: PrefixBit -> InfInteger -> InfInteger -> BitStream -> PERMonad ()
encodeConBS pb l u xs
  =   if u == 0
             then   {- X691REF: 15.8 -}
                    do  putBitstream pb
                        noBit
             else if u == l && u <= 65536
                       then {- X691REF: 15.9 and 15.10 -}
                            do
                              putBitstream pb
                              putBitstream xs
                       else if u <= 65536
                            then {- X691REF: 15.11 (ub set) -}
                                do  putBitstream pb
                                    toNonNegBinaryInteger ((fromInteger . L.genericLength $  xs) - l) (u - l)
                                    putBitstream xs
                            else {- X691REF: 15.11 (ub unset) -}
                                do
                                    putBitstream pb
                                    encodeBitsWithLength xs


\end{code}


{\em encodeNonExtRootBitstring} is similar to {\em encodeExtRootBitstring} but needs the
extension constraint and encodes the L.length of the bitstring as a semi-constrained whole
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
        = do oneBit
             encodeBitsWithLength xs
    | otherwise = throwError (BoundsError "Size out of range")
encodeNonExtRootBitstring nbs rc ec (Valid erc) xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
      in do
          oneBit
          encodeBitsWithLength (namedBitsEdit l u xs)

\end{code}

\section{ENCODING THE OCTETSTRING TYPE}

{\em encodeOctetstring} L.takes the usual two inputs -- the list of serially applied constraints
and the value to be encoded. If the constraint list is empty the function
{\em encodeUnconstrainedOctetstring} is
called. Otherwise, {\em encodeOctetstringWithConstraint} is called. Note that there are two ways
in which a OCTETSTRING type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible since a non-PER visible complete constraint is ignored.
This is determined when generating the effective constraint
for a type using the function {\em lSerialeffectiveCon} defined in the module {\em ConstraintGeneration}.


\begin{code}

encodeOctetstring :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOctetstring [] x
    = {- X691REF: 16.8 with ub unset -}
      encodeUnconstrainedOctetstring x
encodeOctetstring cs x
    = {- X691REF: 16.3 -}
      encodeOctetstringWithConstraint cs x

\end{code}


{\em encodeUnconstrainedOctetstring} encodes an unconstrained octetstring, It uses {\em
encodeUnconstrainedL.length} -- which manages the interleaving of L.length encoding with value
encoding for values with an unconstrained L.length - whose first input {\em encodeOctet}
converts a {\em Word8} representation of an octet to a list of bits representation.

\begin{code}

encodeUnconstrainedOctetstring :: OctetString -> PERMonad ()
encodeUnconstrainedOctetstring (OctetString xs)
    = encodeUnconstrainedLength encodeOctet xs

encodeOctet :: Octet -> PERMonad ()
encodeOctet x = toNonNegBinaryInteger (fromIntegral x) 255

\end{code}

If the constraint is not extensible then {\em encodeNonExtConsOctetstring} is called. If it is
extensible then {\em encodeExtConsOctetstring} is called. They both L.take the effective
constraint and actual constraint associated with the type as input.

\begin{code}

encodeOctetstringWithConstraint :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOctetstringWithConstraint cs v
    = if (not extensible)
        then {- X691REF: 16.4 -}
             encodeNonExtConsOctetstring actualCon effectiveCon v
        else {- X691REF: 16.3 -}
             encodeExtConsOctetstring actualCon effectiveCon v
      where
          effectiveCon :: Either String (ExtensibleConstraint IntegerConstraint)
          effectiveCon = evaluateConstraint  pvOctetStringElements top cs
          actualCon :: Either String (ExtensibleConstraint ValidIntegerConstraint)
          actualCon = evaluateConstraint  pvOctetStringElements top cs
          extensible = eitherExtensible effectiveCon

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

encodeNonExtConsOctetstring :: Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> OctetString
                -> PERMonad ()
encodeNonExtConsOctetstring _ (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf) _ _))
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
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                vrc = getRootConstraint ok

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

encodeExtConsOctetstring :: Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> OctetString
                -> PERMonad()
encodeExtConsOctetstring _
    (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf)
                  (IntegerConstraint NegInf PosInf) _)) vs
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
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                ec = getExtConstraint vsc
                vrc = getRootConstraint ok
                vec = getExtConstraint ok

\end{code}

{\em encodeConstrainedOctetstring} first checks if the value satisfies the constraint.

Note that X.691 16.5 states that if an octetstring is constrained to be of zero L.length then
it shall not be encoded. It is not clear whether this means that an octetstring with no L.length is
not encoded, or if any octetstring associated with a bitstring type with a zero-L.length
constraint is not encoded. We have implemented it using the former case. That is, the
octetstring must satisfy the constraint.

Note that with UNALIGNED PER if the upper bound of a constraint is greater or equal to 64K
then the encoding of the L.length determinant is the same as it would be for an unconstrained
L.length (X691: 10.9.4.2 Note). {\em encodeOctetsWithL.length} which encodes octets with an unconstrained L.length
is used for this case.

\begin{code}

encodeConstrainedOctetstring :: PrefixBit -> InfInteger -> InfInteger -> ValidIntegerConstraint ->
                                OctetStream -> PERMonad ()
encodeConstrainedOctetstring pb l u (Valid vrc) xs
      | inSizeRange xs vrc
         = let exs = encodeOctets xs
           in
             if u == 0
             then   {- X691REF: 16.5 -}
                    return ()
             else if u == l && u <= 65536
                       then {- X691REF: 16.6 and 16.7 -}
                            exs
                       else if u <= 65536
                            then {- X691REF: 16.8 (ub set) -}
                                 let ev = extractValue $ exs
                                 in do encodeEitherOctet ev l u
                                       exs
                            else {- X691REF: 16.8 (ub unset) -}
                                 let ev = extractValue $ exs
                                 in
                                    encodeCase ev encodeOctetsWithLength
       | otherwise = throwError (BoundsError "Size out of range")

encodeEitherOctet (Left s) l u = throwError s
encodeEitherOctet (Right ((),bs)) l u
    = toNonNegBinaryInteger ((fromInteger . toInteger . BL.length . BB.toLazyByteString $ bs) - l) (u - l)

encodeOctets :: OctetStream -> PERMonad ()
encodeOctets (x:xs)
         = mapM_ encodeOctet (x:xs)
encodeOctets [] = return ()

encodeNonExtRootConOctetstring :: IntegerConstraint -> IntegerConstraint
                                   -> ValidIntegerConstraint -> OctetStream -> PERMonad ()
encodeNonExtRootConOctetstring rc ec (Valid erc) xs
    | inSizeRange xs erc
        = let ev = extractValue $ encodeOctets xs
          in do oneBit
                encodeCase ev encodeOctetsWithLength
    | otherwise = throwError (BoundsError "Size out of range")

\end{code}

\section{ENCODING THE SEQUENCE TYPE}

{\em encodeSequence} has only two inputs - the type and value - since a sequence has no PER-visible
constraints. It calls an auxiliary function {\em encodeSequenceAux} which requires two
further inputs which indicate the extensibility of the type and existence of extension
additions (represented as a pair of boolean values), and hosts the bits which indicate the presence or
otherwise of optional or default values. {\em encodeSequenceAux} is a recursive function that recurses over
the structure of a sequence and returns a value of type {\em PERMonad (OptDefBits, BitStream -> BitStream)}.
This is a monadic value that outputs (the encoding) bits and returns a
pair of values -- the optional or default value indicator bits and a function which adds the appropriate
prefix to the output that indicates whether the encoded value is extensible and has any extension additions,
and the optional/default indicator bits.

{\em encodeSequenceAux} has several cases to deal with that match the various components of a sequence
-- mandatory, optional, default, extension marker and so on -- and
returns a pair whose second component is the function
{\em completeSequenceBits} which adds a prefix to the output bits including the extension bit if
required and the bits which describe the presence or otherwise of optional or default values.
Each root component is encoded as required using {\em encode}.

Note that the extension indicator is initally set to {\em (False, False)}. The first element is converted
to {\em True} when an extension marker is reached and {\em encodeSequenceAuxExt} is called.
It returns a value of type
{\em PERMonad ((ExtAndUsed, ExtBits, OptDefBits, PERMonad (OptDefBits, BitStream -> BitStream)))}.
That is, it is a monadic value that writes (the encoding) bitstream and returns 4 values in a 4-tuple.
These are:
\begin{itemize}
\item
an updated extension indicator reflecting whether any extension additions exist in the value;
\item
a bitstream representing the existence or otherwise of extension additions;
\item
a bitstream representing the existence or otherwise of optional or default components; and
\item
a monadic value which is the result of applying {\em encodeSequenceAux} to the remainder of the sequence once
the extension additions have been terminated. This is indicated by another extension marker or simply by the
end of the sequence.
\end{itemize}

Since we need to output root value encodings before extension addition encodings, we need
to run the returned {\em encodeSequenceAux} monad in advance of outputing the extension addition
encoding bits. This is achieved by using the {\em MonadWriter} function {\em censor} which applies
a function to the output of a monad in advance of outputting. Here we apply the Haskell built-in
function {\tt const} which simply returns its first argument -- in this case the empty list {\em []}.
Now since this function is applied lazily the monad can run without producing output but returning the
monad that we
require. We then run the returned monad and then run the extension addition monad again but this time
apply a function to add the required preamble to the extension addition encoding bits using the
function {\em addExtensionAdditionPreamble}.

Note also that the encoding of a {\em COMPONENTS OF} item is managed by
{\em encodeSequenceAuxCO}. This monadic function outputs the encoding bits and returns the
optional/default bits to be used in the generation of the encoding preamble.

\begin{code}
type OptDefBits = BitStream
type ExtBits = BitStream
type ExtAndUsed = (Bool, Bool)

encodeSequence :: Sequence a -> a -> PERMonad ()
encodeSequence s v
           = do _odbs <- pass $ encodeSequenceAux (False, False) [] s v
                return ()

-- FIXME: Eugh pattern match failure here
selectOutput (Right (a,b)) = b
selectOutput (Left s)      = error $ show s

encodeSequenceAux :: ExtAndUsed ->
                     OptDefBits ->
                     Sequence a ->
                     a ->
                     PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)
encodeSequenceAux extAndUsed optDef EmptySequence Empty
    = return (optDef, completeSequenceBits extAndUsed optDef)
encodeSequenceAux (extensible, b) optDef (ExtensionMarker as) xs
    | not extensible
        = let m = encodeSequenceAuxExt (True, False) optDef [] as xs
          in

           do (b, eb, od, pm) <- censor (const BB.empty) m
              (od2,f) <- pm

--            do rec (b, eb, _, pm) <- trace "Censor" $ censor (BB.append foo) m
--                   ((), foo)       <- listen $ addExtensionAdditionPreamble eb
--               od2 <- fst <$> pm

              {- X691REF: 18.8 -}
              censor (BB.append (selectOutput . extractValue $ addExtensionAdditionPreamble eb)) m
              encodeSequenceAux b od2 EmptySequence Empty
    | otherwise
        = encodeSequenceAux (extensible,b) optDef as xs
encodeSequenceAux eu od (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do od2 <- encodeSequenceAuxCO [] s x
         encodeSequenceAux eu (od ++ od2) as xs
encodeSequenceAux eu od (AddComponent (ComponentsOf (ReferencedType n t)) as) (x:*:xs)
    = encodeSequenceAux eu od (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSequenceAux eu od (AddComponent (ComponentsOf (ConstrainedType t c)) as) (x:*:xs)
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
    = do {- X691REF: 18.2 with optional component present -}
         encode a [] x
         encodeSequenceAux eu (od ++ [1]) as xs
encodeSequenceAux eu od (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with default value -}
        {- X691REF: 18.5 with default value (CANONICAL-PER) -}
        encodeSequenceAux eu (od ++ [0]) as xs
encodeSequenceAux eu od (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do {- X691REF: 18.2 with non-default value -}
         encode a [] x
         encodeSequenceAux eu (od ++ [1]) as xs
encodeSequenceAux (b1,b2) od (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeSequenceAux (b1,True) od as xs
\end{code}

completeSequenceBits changed so that the collection of optional/default
bits are implemented using Data.Seq.

\begin{code}
completeSequenceBits :: ExtAndUsed -> BitStream -> BB.BitBuilder -> BB.BitBuilder
completeSequenceBits (extensible, extensionAdditionPresent) odb bs
    | not extensible
        = BB.append (fragment odb) bs
    | extensionAdditionPresent
        {- X691REF: 18.1 with extension additions present -}
        {- X691REF: 18.2  -}
        = BB.append (BB.singleton True) $ BB.append (fragment odb) bs
    | otherwise
        {- X691REF: 18.1 with no extenion additions present -}
        {- X691REF: 18.2  -}
        = BB.append (BB.singleton False) $ BB.append (fragment odb) bs
    where
        {- X691REF: 18.3  -}
        fragment ls
            | L.length ls < 64 * 2^10
                = toBitBuilder ls
            | otherwise
                = let Right ((),b) = extractValue $ encodeUnconstrainedLength (tell . BB.fromBits 1) ls
                                    in
                                        b


toBitBuilder (f:r) = BB.append (BB.fromBits 1 f) (toBitBuilder r)
toBitBuilder [] = BB.empty
\end{code}

\begin{code}
encodeSequenceAuxExt :: ExtAndUsed -> OptDefBits -> ExtBits -> Sequence a -> a
                        -> PERMonad ((ExtAndUsed, ExtBits, OptDefBits,
                                        PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)))
encodeSequenceAuxExt b odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSequenceAuxExt b odb (eb ++ [0]) as xs
encodeSequenceAuxExt (b1,b2) odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ComponentType extension -}
         encodeOpen a x
         encodeSequenceAuxExt (b1,True) odb (eb ++ [1]) as xs
encodeSequenceAuxExt b odb eb (ExtensionAdditionGroup _ a as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSequenceAuxExt b odb (eb ++ [0]) as xs
encodeSequenceAuxExt (b1,b2) odb eb (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ExtensionAdditionGroup extension -}
         encodeOpen (BuiltinType (SEQUENCE (makeSequence a))) x
         encodeSequenceAuxExt (b1, True) odb (eb ++ [1]) as xs
encodeSequenceAuxExt b odb eb (ExtensionMarker as) xs
    = return (b, eb, odb, encodeSequenceAux b odb as xs)
encodeSequenceAuxExt b odb eb EmptySequence Empty
    | L.null eb
        = return (b, eb, odb, encodeSequenceAux b odb EmptySequence Empty)
    | otherwise
        = return (b, eb, odb, encodeSequenceAux b odb EmptySequence Empty)
encodeSequenceAuxExt b odb eb _ _
    = throwError (OtherError "Inappropriate component!")
\end{code}


\begin{code}
addExtensionAdditionPreamble :: OptDefBits -> PERMonad ()
addExtensionAdditionPreamble ap
    = let la = genericLength ap
       in trace (show la) $ if la <= 63
        then do trace (show "ZERO") $ return ()
                zeroBit
                toNonNegBinaryInteger (la - 1) 63
                tell (toBitBuilder ap)
        else do trace (show "ONE") $ return ()
                oneBit
                encodeNonNegBinaryIntInOctets la
                tell (toBitBuilder ap)
\end{code}

When encoding a ComponentsOf component, we simply extract and encode the root components of
the type.

\begin{code}

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

\begin{code}

dSequence :: Sequence a -> UnPERMonad a
dSequence s =
   do ps <- lift $ bitMask (l s)
      dSequenceAux ps s

l :: Integral n => Sequence a -> n
l EmptySequence = 0
l (AddComponent (MandatoryComponent _) ts) = l ts
l (AddComponent (OptionalComponent  _) ts) = 1 + (l ts)

bitMask n = sequence $ L.take n $ repeat $ BG.getBit

type BitMap = [Bool]

-- FIXME: We don't yet seem to handle e.g. OptionalComponent
dSequenceAux :: BitMap -> Sequence a -> UnPERMonad a
-- FIXME: Ignoring the bit map doesn't look right - it's probably an error if it's not empty
dSequenceAux _ EmptySequence = return Empty
dSequenceAux bitmap (AddComponent (MandatoryComponent (NamedType _ t)) ts) =
   do x <- decode t []
      xs <- dSequenceAux bitmap ts
      return (x :*: xs)

\end{code}

\section{ENCODING THE SEQUENCE-OF TYPE}

{\em encodeSequenceOf} takes three inputs, the usual two inputs -- the list of serially applied constraints
and the value to be encoded -- and the type of the components. This is required as input to the {\em encode} function
which encodes each component of the SEQUENCEOF. If the constraint list is empty the function
{\em encodeUnconstrainedSequenceOf} is
called. Otherwise, {\em encodeSequenceOfWithConstraint} is called. Note that there are two ways
in which a SEQUENCEOF type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible. This is determined when generating the effective constraint
for a type using the function {\em lSerialeffectiveCon} defined in the module {\em
ConstraintGeneration}.

Note that a SEQUENCEOF value is represented as a Haskell list of components. The PER-visible
SIZE constraint is applied to the number of elements in the list.

\begin{code}

encodeSequenceOf :: [SubtypeConstraint [a]] -> ASNType a -> [a] -> PERMonad ()
encodeSequenceOf [] t x
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSequenceOf t x
encodeSequenceOf cl t x
    =   encodeSequenceOfWithConstraint t cl x

\end{code}

{\em encodeUnconstrainedSequenceOf} encodes an unconstrained SEQUENCEOF value by adding a
length determinant to the encoding of the SEQUENCEOF components. This may of course involve
fragmentation.

\begin{code}

encodeUnconstrainedSequenceOf :: ASNType a -> [a] -> PERMonad ()
encodeUnconstrainedSequenceOf t xs = encodeUnconstrainedLength (encode t []) xs

\end{code}


{\em encodeSequenceOfWithConstraint} calls {\em encodeNonExtConsSequenceOf} if the constraint is not
extensible. If it is extensible then {\em encodeExtConsSequenceOf} is called. They both take the
effective constraint and actual constraint associated with the type as input.

\begin{code}

encodeSequenceOfWithConstraint :: ASNType a -> [SubtypeConstraint [a]] -> [a]
                                  -> PERMonad ()
encodeSequenceOfWithConstraint t cs v
    = if (not extensible)
        then
             encodeNonExtConsSequenceOf t actualCon effectiveCon v
        else {- X691REF: 19.4 -}
             encodeExtConsSequenceOf t actualCon effectiveCon v
      where
          effectiveCon :: Either String (ExtensibleConstraint IntegerConstraint)
          effectiveCon = evaluateConstraint  pvSequenceOfElements top cs
          actualCon :: Either String (ExtensibleConstraint ValidIntegerConstraint)
          actualCon = evaluateConstraint  pvSequenceOfElements top cs
          extensible = eitherExtensible effectiveCon

\end{code}

{\em encodeNonExtConsSequenceOf} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedSequenceOf} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedSequenceOf} is called.
\end{itemize}

\begin{code}

encodeNonExtConsSequenceOf :: ASNType a -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> [a]
                -> PERMonad ()
encodeNonExtConsSequenceOf t _ (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf) _ _)) vs
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSequenceOf t vs
encodeNonExtConsSequenceOf t (Right ok) (Right vsc) vs
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = {- X691REF: 19.5 - 19.6 -}
             encodeConstrainedSequenceOf t [] l u vrc vs
             where
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                vrc = getRootConstraint ok

\end{code}

{\em encodeExtConsSequenceOf} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedSequenceOf} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedSequenceOf} is called with the
prefix bit set to 0. If this results in an error (the value cannot satisfy the constraint root)
then {\em encodeExtConstrainedSequenceOf} is called and the prefix bit is set to 1. The function
Haskell library function {\em catchError} manages the error/non-error cases.
\end{itemize}


\begin{code}

encodeExtConsSequenceOf :: ASNType a -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> [a]
                -> PERMonad()
encodeExtConsSequenceOf t _
    (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf)
                  (IntegerConstraint NegInf PosInf) _)) vs
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSequenceOf t vs
encodeExtConsSequenceOf t (Right ok) (Right vsc) vs
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = do
                catchError (do {- X691REF: 19.4 within root -}
                               encodeConstrainedSequenceOf t [0] l u vrc vs)
                           (\err -> do {- X691REF: 19.4 not in root -}
                                       encodeNonExtRootConSequenceOf t rc ec vec vs)
             where
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                ec = getExtConstraint vsc
                vrc = getRootConstraint ok
                vec = getExtConstraint ok

\end{code}


{\em encodeConstrainedSequenceOf} first checks if the value satisfies the constraint.
Note that with UNALIGNED PER if the upper bound of a constraint is greater or equal to 64K
then the encoding of the length determinant is the same as it would be for an unconstrained
length (X691: 10.9.4.2 Note).


\begin{code}

encodeConstrainedSequenceOf :: ASNType a -> PrefixBit -> InfInteger -> InfInteger
                               -> ValidIntegerConstraint -> [a] -> PERMonad ()
encodeConstrainedSequenceOf t pb l u (Valid vrc) xs
      | inSizeRange xs vrc
         = if u == l && u <= 65536
              then {- X691REF: 19.5 -}
                   do tell $ toBitBuilder pb
                      mapM_ (encode t []) xs
              else if u <= 65536
                   then {- X691REF: 19.6 with ub set -}
                        do tell $ toBitBuilder pb
                           toNonNegBinaryInteger ((fromInteger . genericLength $ xs) - l) (u - l)
                           mapM_ (encode t []) xs
                   else {- X691REF: 19.6 with ub unset -}
                        do tell $ toBitBuilder pb
                           encodeUnconstrainedSequenceOf t xs
      | otherwise = throwError (BoundsError "Size out of range")



encodeNonExtRootConSequenceOf :: ASNType a -> IntegerConstraint -> IntegerConstraint
                                 -> ValidIntegerConstraint -> [a] -> PERMonad ()
encodeNonExtRootConSequenceOf t rc ec (Valid erc) xs
    | inSizeRange xs erc
        = do oneBit
             encodeUnconstrainedSequenceOf t xs
    | otherwise = throwError (BoundsError "Size out of range")

\end{code}

\section{ENCODING THE SET TYPE}

{\em encodeSet} encodes a SET value. In common with a SEQUENCE, a SET has no PER-visible
constraints and thus the encoding function has only two inputs: the type of the set to be
encoded represented as a sequence, and the value to be encoded. The encoding of a set is
similar to that of a sequence except that the root components are encoded in order of their
tags. We therefore cannot output each root component encoding in the order they appear in the
set value, but instead, must store the monadic encode value, typically of the form {\em
encode a [] x}, in a list, which are then ordered by tag value, and then run in this order. That is, the
encoding bits are only output after the ordering of the components. This behaviour
is managed by the auxiliary function {\em encodeSetAux} which is similar to {\em
encodeSequenceAux} except that the second input is a list of pairs of
\begin{itemize}
\item
tag information and
\item
a pair of optional/default bit with the monadic encode value
\end{itemize}
instead of simply a list of optional/default bits. Here each optional/default bit is of the
type {\em Maybe Int} to allow for non-optional/default components for which the entry will be
{\em Nothing}.

\begin{code}

encodeSet :: Sequence a -> a -> PERMonad ()
encodeSet s v
           = do odb <- pass $ encodeSetAux (False, False) [] s v
                return ()

encodeSetAux :: ExtAndUsed -> [(TagInfo, (Maybe Int, PERMonad ()))] -> Sequence a -> a
                -> PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)
encodeSetAux eu ms EmptySequence Empty
    =   let sms = L.sortBy firstItem ms
            firstItem m n
                | fst m < fst n = LT
                | fst m == fst n = EQ
                | otherwise = GT
            odb = L.map (\(Just x) -> x) $ L.filter (/= Nothing) $  L.map (fst . snd) sms
            mds = L.map (snd . snd) sms
        in do {- FIXME run monads in the right order and create optdefbits-}
                 mapM_ id mds
                 return (odb, completeSequenceBits eu odb)
encodeSetAux (extensible, b) ms (ExtensionMarker as) xs
    | not extensible
        = let m = encodeSetAuxExt (True, False) ms [] as xs
          in
           do (b, eb,pm) <- censor (const BB.empty) m
              (od2,f) <- pm
              {- X691REF: 18.8 -}
              censor (BB.append (selectOutput . extractValue $ addExtensionAdditionPreamble eb)) m
              encodeSequenceAux b od2 EmptySequence Empty
    | otherwise
        = encodeSetAux (extensible,b) ms as xs
encodeSetAux eu ms (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do ms2 <- encodeSetAuxCO [] s x
         encodeSetAux eu (ms ++ ms2) as xs
encodeSetAux eu ms (AddComponent (ComponentsOf (ReferencedType n t)) as) (x:*:xs)
    = encodeSetAux eu ms (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSetAux eu ms (AddComponent (ComponentsOf (ConstrainedType t c)) as) (x:*:xs)
    = encodeSetAux eu ms (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSetAux eu ms (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = encodeSetAux eu (ms ++ [(getTI a, (Nothing, encode a [] x))])  as xs
encodeSetAux eu ms (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    = encodeSetAux eu ms as xs
encodeSetAux (b1,b2) ms (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = encodeSetAux (b1, True) ms as xs
encodeSetAux eu ms (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with optional component not present -}
        encodeSetAux eu (ms ++ [(getTI a, (Just 0, noBit))])  as xs
encodeSetAux eu ms (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    =   {- X691REF: 18.2 with optional component present -}
        encodeSetAux eu (ms ++ [(getTI a, (Just 1, encode a [] x))]) as xs
encodeSetAux eu ms (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with default value -}
        {- X691REF: 18.5 with default value (CANONICAL_PER) -}
        encodeSetAux eu (ms ++ [(getTI a, (Just 0, noBit))])  as xs
encodeSetAux eu ms (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    =   {- X691REF: 18.2 with default component present -}
        encodeSetAux eu (ms ++ [(getTI a, (Just 1, encode a [] x))]) as xs
encodeSetAux (b1,b2) ms (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeSetAux (b1,True) ms as xs



encodeSetAuxExt :: ExtAndUsed -> [(TagInfo, (Maybe Int, PERMonad ()))]  -> ExtBits -> Sequence a -> a
                        -> PERMonad ((ExtAndUsed, ExtBits,
                                PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)))
encodeSetAuxExt b ms eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSetAuxExt b ms (eb ++ [0]) as xs
encodeSetAuxExt (b1,b2) ms eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ComponentType extension -}
         encodeOpen a x
         encodeSetAuxExt (b1,True) ms (eb ++ [1]) as xs
encodeSetAuxExt b ms eb (ExtensionAdditionGroup _ a as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSetAuxExt b ms (eb ++ [0]) as xs
encodeSetAuxExt (b1,b2) ms eb (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ExtensionAdditionGroup extension -}
         encodeOpen (BuiltinType (SEQUENCE (makeSequence a))) x
         encodeSetAuxExt (b1, True) ms (eb ++ [1]) as xs
encodeSetAuxExt b ms eb (ExtensionMarker as) xs
    = return (b, eb, encodeSetAux b ms as xs)
encodeSetAuxExt b ms eb EmptySequence Empty
    | L.null eb
        = return (b, eb, encodeSetAux b ms EmptySequence Empty)
    | otherwise
        = return (b, eb, encodeSetAux b ms EmptySequence Empty)
encodeSetAuxExt b odb eb _ _
    = throwError (OtherError "Inappropriate component!")

\end{code}


When encoding a ComponentsOf component, we simply extract and encode the root components of
the type.

\begin{code}

encodeSetAuxCO :: [(TagInfo, (Maybe Int, PERMonad ()))] -> Sequence a -> a
                       -> PERMonad [(TagInfo, (Maybe Int, PERMonad ()))]
encodeSetAuxCO ms EmptySequence _
    = return ms
encodeSetAuxCO ms (ExtensionMarker as) xs
    = encodeSetAuxCO ms as xs
encodeSetAuxCO ms (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do ms2 <- encodeSetAuxCO [] s x
         encodeSetAuxCO (ms ++ ms2) as xs
encodeSetAuxCO odb (AddComponent (ComponentsOf _) as) (x:*:xs)
    = throwError (OtherError "COMPONENTS OF can only be applied to a SEQUENCE")
encodeSetAuxCO ms (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = encodeSetAuxCO (ms ++ [(getTI a, (Nothing, encode a [] x))])  as xs
encodeSetAuxCO odb (AddComponent (ExtensionComponent (NamedType t a)) as) (_:*:xs)
    = encodeSetAuxCO odb as xs
encodeSetAuxCO ms (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs)
    = encodeSetAuxCO (ms ++ [(getTI a, (Just 0, noBit))])  as xs
encodeSetAuxCO ms (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = encodeSetAuxCO (ms ++ [(getTI a, (Just 1, encode a [] x))])  as xs
encodeSetAuxCO ms (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    = encodeSetAuxCO (ms ++ [(getTI a, (Just 0, noBit))])  as xs
encodeSetAuxCO ms (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = encodeSetAuxCO (ms ++ [(getTI a, (Just 1, encode a [] x))])  as xs
encodeSetAuxCO ms (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeSetAuxCO ms as xs

\end{code}



\section{ENCODING THE SET-OF TYPE}

SET-OF types are encoded as SEQUENCE-OF types except that CANONICAL-PER requires that the component
values of a SET-OF type are encoded in ascending order of their same-length encodings. That is, each
encoding is converted to a integral multiple of octet encoding by appending with 0 bits, and then
these are converted to the same length as the longest encoding by appending 0-octets.

\begin{code}

encodeSetOf :: [SubtypeConstraint [a]] -> ASNType a -> [a] -> PERMonad ()
encodeSetOf [] t x
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSetOf t x
encodeSetOf cl t x
    =   encodeSetOfWithConstraint t cl x

encodeUnconstrainedSetOf :: ASNType a -> [a] -> PERMonad ()
encodeUnconstrainedSetOf t xs
    = do {- X691REF: 21.1 -}
         ols <- orderedSetOf t xs
         encodeUnconstrainedLength tell ols

\end{code}

The function {\em orderedSetOf} orders the component value encodings as required by X691: 21.1.

\begin{code}

orderedSetOf :: ASNType a -> [a] -> PERMonad [BB.BitBuilder]
orderedSetOf t ls
    = let els = map (selectOutput . extractValue . encode t []) ls
        --  pls = map padBits els
        --  nls = zipWith (++) els pls
          nls = map BB.toLazyByteString els
          long = maximum (map BL.length  nls)
          xls = map (\x -> appendZeroes (long - (BL.length x))BL.empty) nls
          ols = L.zip (L.zipWith BL.append nls xls) els
      in
          return (L.map snd (L.sortBy order ols))


{-
padBits :: BB.BitBuilder -> BB.BitBuilder
padBits enc
    = let le  = length enc
          bts = le `mod` 8
          pad = if bts == 0
                           then []
                           else take (8-bts) [0,0..]
      in pad
-}
appendZeroes :: Int64 -> BL.ByteString -> BL.ByteString
appendZeroes i bs
    = if i == 0 then bs
                else appendZeroes (i-1) (BL.append bs  zero)

zero :: BL.ByteString
zero = BL.singleton 0

order :: (BL.ByteString, BB.BitBuilder) -> (BL.ByteString, BB.BitBuilder) -> Ordering
order (f,s) (x,y)
    | f < x = LT
    | f == x = EQ
    | otherwise = GT

\end{code}



{\em encodeSetOfWithConstraint} calls {\em encodeNonExtConsSetOf} if the constraint is not
extensible. If it is extensible then {\em encodeExtConsSetOf} is called. They both take the
effective constraint and actual constraint associated with the type as input.

\begin{code}

encodeSetOfWithConstraint :: ASNType a -> [SubtypeConstraint [a]] -> [a]
                                  -> PERMonad ()
encodeSetOfWithConstraint t cs v
    = if (not extensible)
        then
             encodeNonExtConsSetOf t actualCon effectiveCon v
        else {- X691REF: 19.4 -}
             encodeExtConsSetOf t actualCon effectiveCon v
      where
          effectiveCon :: Either String (ExtensibleConstraint IntegerConstraint)
          effectiveCon = evaluateConstraint  pvSequenceOfElements top cs
          actualCon :: Either String (ExtensibleConstraint ValidIntegerConstraint)
          actualCon = evaluateConstraint  pvSequenceOfElements top cs
          extensible = eitherExtensible effectiveCon

\end{code}

{\em encodeNonExtConsSetOf} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedSetOf} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedSetOf} is called.
\end{itemize}

\begin{code}

encodeNonExtConsSetOf :: ASNType a -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> [a]
                -> PERMonad ()
encodeNonExtConsSetOf t _ (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf) _ _)) vs
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSetOf t vs
encodeNonExtConsSetOf t (Right ok) (Right vsc) vs
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = {- X691REF: 19.5 - 19.6 -}
             encodeConstrainedSetOf t [] l u vrc vs
             where
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                vrc = getRootConstraint ok

\end{code}

{\em encodeExtConsSetOf} has to deal with three cases.
\begin{itemize}
\item
There are no PER-visible constraints. The function {\em encodeUnconstrainedSetOf} is
called.
\item
The constraint is empty and thus no values can be encoded. Note that this means that there is a
PER-visible size constraint that has no values. An appropriate error is thrown.
\item
There is a PER-visible constraint. The function {\em encodeConstrainedSetOf} is called with the
prefix bit set to 0. If this results in an error (the value cannot satisfy the constraint root)
then {\em encodeExtConstrainedSetOf} is called and the prefix bit is set to 1. The function
Haskell library function {\em catchError} manages the error/non-error cases.
\end{itemize}


\begin{code}

encodeExtConsSetOf :: ASNType a -> Either String (ExtensibleConstraint ValidIntegerConstraint)
                -> Either String (ExtensibleConstraint IntegerConstraint)
                -> [a]
                -> PERMonad()
encodeExtConsSetOf t _
    (Right (ExtensibleConstraint (IntegerConstraint NegInf PosInf)
                  (IntegerConstraint NegInf PosInf) _)) vs
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSetOf t vs
encodeExtConsSetOf t (Right ok) (Right vsc) vs
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = do
                catchError (do {- X691REF: 19.4 within root -}
                               encodeConstrainedSetOf t [0] l u vrc vs)
                           (\err -> do {- X691REF: 19.4 not in root -}
                                       encodeNonExtRootConSetOf t rc ec vec vs)
             where
                rc = getRootConstraint vsc
                l = lower rc
                u = upper rc
                ec = getExtConstraint vsc
                vrc = getRootConstraint ok
                vec = getExtConstraint ok

\end{code}


{\em encodeConstrainedSetOf} first checks if the value satisfies the constraint.
Note that with UNALIGNED PER if the upper bound of a constraint is greater or equal to 64K
then the encoding of the length determinant is the same as it would be for an unconstrained
length (X691: 10.9.4.2 Note).


\begin{code}

encodeConstrainedSetOf :: ASNType a -> PrefixBit -> InfInteger -> InfInteger
                               -> ValidIntegerConstraint -> [a] -> PERMonad ()
encodeConstrainedSetOf t pb l u (Valid vrc) xs
      | inSizeRange xs vrc
         = if u == l && u <= 65536
              then {- X691REF: 19.5 -}
                   do tell $ toBitBuilder pb
                      ols <- orderedSetOf t xs
                      mapM_ tell ols
              else if u <= 65536
                   then {- X691REF: 19.6 with ub set -}
                        do tell $ toBitBuilder pb
                           toNonNegBinaryInteger ((fromInteger . genericLength $  xs) - l) (u - l)
                           {- X691REF: 21.1 -}
                           ols <- orderedSetOf t xs
                           mapM_ tell ols
                   else {- X691REF: 19.6 with ub unset -}
                        do tell $ toBitBuilder pb
                           encodeUnconstrainedSetOf t xs
      | otherwise = throwError (BoundsError "Size out of range")



encodeNonExtRootConSetOf :: ASNType a -> IntegerConstraint -> IntegerConstraint
                                 -> ValidIntegerConstraint -> [a] -> PERMonad ()
encodeNonExtRootConSetOf t rc ec (Valid erc) xs
    | inSizeRange xs erc
        = do oneBit
             encodeUnconstrainedSetOf t xs
    | otherwise = throwError (BoundsError "Size out of range")

\end{code}

\section{ENCODING THE CHOICE TYPE}

{\em encodeChoice} encodes CHOICE values. It is not dissimilar to
{\em encodeSet} in that the possible choice components must be
assigned an index based on their canonical ordering. This index,
which starts from 0, prefixes the value encoding and is absent if
there is only a single choice.

\begin{code}

encodeChoice :: Choice a -> ExactlyOne a SelectionMade -> PERMonad ()
encodeChoice c x
   = let (b,(r,e)) = getCTags True ([],[]) c
         {- X691REF: 22.2 -}
         ids = assignIndices (r,e)
     in
        encodeChoiceAux (b,ids) c x


type ChoiceRootIndices = [Int]
type ChoiceExtIndices = [Int]

assignIndices :: (ChoiceRootTags, ChoiceExtTags) -> (ChoiceRootIndices, ChoiceExtIndices)
assignIndices (r,e)
    = let ri = indices r
          re = indices e
      in
        (ri,re)

indices :: Ord a => [a] -> [Int]
indices xs
    = let sxs = L.sort xs
      in
        map (\(Just x) -> x) (indices' xs sxs)

indices' :: Eq a => [a] -> [a] -> [Maybe Int]
indices' [] sxs = []
indices' (f:r) sxs
        = (elemIndex f sxs : indices' r sxs)

\end{code}

The auxilliary function {\em encodeChoiceAux} manages the various choice cases. The cases are:

\begin{itemize}
\item
if no choice is chosen as indicated by the constructor {\em EmptyChoice} then an error is
thrown;
\item
an extension marker results in the function {\em encodeChoiceExtAux} being called. This deals
with a choice that is not chosen from the extension root;
\item
if a root option is not chosen then the function {\em encodeChoiceAux'} is called. This
indicates that there is at least two root options and thus the index must be encoded;
\item
if the first root option is chosen and there is only one root index as indicated by the
Haskell singleton list {\em [f]}, then the choice index is not encoded. The encoding of the
choice value is prefixed by a {\em 0} bit is the type is extensible;
\item
an extension addition group suggests an erroneous CHOICE type since this can only appear after
an extension marker.
\end{itemize}

The function {\em encodeChoiceAux'} is similar to {\em encodeChoiceAux} except that there is
not single root choice case.

\begin{code}

type NoExtension = Bool

encodeChoiceAux :: (NoExtension, (ChoiceRootIndices, ChoiceExtIndices))
                    -> Choice a -> ExactlyOne a n -> PERMonad ()
encodeChoiceAux ids EmptyChoice _ = throwError (OtherError "No choice value!")
encodeChoiceAux ids (ChoiceExtensionMarker as) xs = encodeChoiceExtAux ids as xs
encodeChoiceAux (b,(f:r,e)) (ChoiceOption a as) (AddNoValue x xs)
     =  let l = genericLength r
        in encodeChoiceAux' l (b,(r,e)) as xs
encodeChoiceAux (b, ([f],e)) (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do
        if b then   {- X691REF: 22.4, 22.5 and 22.7 -}
                    zeroBit
             else   {- X691REF: 22.4 and 22.6 -}
                    return ()
        encode a [] x
encodeChoiceAux (b, ((f:g:r),e)) (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do
        if b then   {- X691REF: 22.5 and 22.7 -}
                    zeroBit
             else   {- X691REF: 22.6 -}
                    oneBit -- tell []
        toNonNegBinaryInteger (fromInteger . toInteger $ f) (fromInteger . genericLength $ g:r)
        encode a [] x
encodeChoiceAux _ (ChoiceExtensionAdditionGroup _ _ ) _
    = throwError (OtherError "Impossible case: EXTENSION ADDITION GROUP only appears in an extension.")

encodeChoiceAux' :: Integer -> (NoExtension, (ChoiceRootIndices, ChoiceExtIndices))
                    -> Choice a -> ExactlyOne a n -> PERMonad ()
encodeChoiceAux' l ids EmptyChoice _ = throwError (OtherError "No choice value!")
encodeChoiceAux' l ids (ChoiceExtensionMarker as) xs = encodeChoiceExtAux ids as xs
encodeChoiceAux' l (b,(f:r,e)) (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceAux' l (b,(r,e)) as xs
encodeChoiceAux' l (b, (f:r,e)) (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do
        tell $ BB.singleton b
        toNonNegBinaryInteger (fromInteger . toInteger $ f) (fromInteger l)
        encode a [] x
encodeChoiceAux' _ _ (ChoiceExtensionAdditionGroup _ _ ) _
    = throwError (OtherError "Impossible case: EXTENSION ADDITION GROUP only appears in an extension.")

\end{code}

The function {\em encodeChoiceExtAux} processes values that are not in the extension root of a
CHOICE type. It is similar to {\em encodeChoiceAux} except that:
\begin{itemize}
\item
an extension addition group is a valid component and results in its components being
processed;
\item
if the chosen value is in the extension then the choice index is encoded as a normally small
non-negative integer, the value is encoded as an open type value, and these encodings are
prefixed by a single {\em 1} bit.
\end{itemize}

\begin{code}

encodeChoiceExtAux :: (NoExtension, (ChoiceRootIndices, ChoiceExtIndices))
                    -> Choice a -> ExactlyOne a n -> PERMonad ()
encodeChoiceExtAux ids EmptyChoice _ = throwError (OtherError "No choice value!")
encodeChoiceExtAux ids(ChoiceExtensionMarker as) xs =
   encodeChoiceAux ids as xs
encodeChoiceExtAux ids (ChoiceExtensionAdditionGroup _ as) xs =
   encodeChoiceExtAux' ids as xs
encodeChoiceExtAux (b,(r, (f:e))) (ChoiceOption a as) (AddNoValue x xs) =
   encodeChoiceExtAux (b, (r,e)) as xs
encodeChoiceExtAux (b,(r, (f:e))) (ChoiceOption (NamedType t a) as) (AddAValue x xs)
    = do {- X691REF: 22.5 and 22.8 -}
         oneBit
         encodeNSNNInt (toInteger f) 0
         encodeOpen a x


encodeChoiceExtAux' :: (NoExtension, (ChoiceRootIndices, ChoiceExtIndices))
                    -> Choice' a -> ExactlyOne a n -> PERMonad ()
encodeChoiceExtAux' ids EmptyChoice' _ = throwError (OtherError "No choice value!")
encodeChoiceExtAux' ids ChoiceExtensionMarker' _ = throwError (OtherError "No choice value!")
encodeChoiceExtAux' (b,(r, (f:e))) (ChoiceOption' a as) (AddNoValue x xs) =
   encodeChoiceExtAux' (b, (r,e)) as xs
encodeChoiceExtAux' (b,(r, (f:e))) (ChoiceOption' (NamedType t a) as) (AddAValue x xs)
    = do {- X691REF: 22.5 and 22.8 -}
         oneBit
         encodeNSNNInt (toInteger f) 0
         encodeOpen a x

\end{code}

\section{ENCODING THE RESTRICTED CHARACTER STRING TYPES}

There are two categories of restricted character string types -- known-multiplier character
strings and others. We have currently only implemented the known-multiplier category.

{\em encodeKMS} takes the usual two inputs -- the list of serially applied constraints
and the value to be encoded. If the constraint list is empty the function
{\em encodeUnconstrainedKMS} is
called. Otherwise, {\em encodeKMSWithConstraint} is called. Note that there are two ways
in which a known-multiplier string type may have no PER-visible constraints. The first is when there are no
constraints associated with the type. The second is when all of the serially applied
constraints are non-PER visible since a non-PER visible complete constraint is ignored.
This is determined when generating the effective constraint
for a type using the function {\em lSerialeffectiveCon} defined in the module {\em ConstraintGeneration}.

Note that {\em encodeKMS} is a constrained polymorphic type that applies to a set of
known-multiplier string types. Each is a member of three type classes:

\begin{itemize}
\item
{\em Eq} so that there values can be tested for equality;
\item
{\em RS} a type class of restricted string types defined in the module {\em LatticeMod}. It
include methods to access the string from a restricted value and vice versa; and
\item
{\em Lattice} a type class also defined in {\em LatticeMod}. It specifies all of the
behavioural requirements of a {\bf bounded lattice} such as join and meet operations and a
greatest ({\em top}) and least ({\em bottom}) element. Note that each type will have its own
greatest element which is the complete set of possible values as defined in X.691 27.5.3.
\end{itemize}

\begin{code}

encodeKMS :: (Eq a, RS a, Lattice a)
              => SerialSubtypeConstraints a -> a -> PERMonad ()
encodeKMS [] x
    = {- X691REF: 27.5.1 with no permitted alphabet constraint -}
      encodeUnconstrainedKMS x
encodeKMS cs x
    = encodeKMSWithConstraint cs x

c11 :: Either String (ExtensibleConstraint (ResStringConstraint VisibleString IntegerConstraint))
c11 = evaluateSingleConstraint   False pvKnownMultiplierElements extCon3

c12 :: Either String (ExtensibleConstraint (ResStringConstraint VisibleString IntegerConstraint))
c12 = evaluateSingleConstraint   False pvKnownMultiplierElements pac1

pac1 :: SubtypeConstraint VisibleString
pac1 = RootOnly (UnionSet (UnionMark ( NoUnion (NoIntersection (ElementConstraint (SZ (SC (RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (V (R (1,5)))))))))))))
             (NoIntersection (ElementConstraint (P (FR (RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "dan"))))))))))))))

extCon :: SubtypeConstraint VisibleString
extCon = RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (P (FR (NonEmptyExtension
                (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "ABC")))))))
                (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))))

extCon3 :: SubtypeConstraint VisibleString
extCon3 = RootOnly (UnionSet ( NoUnion (NoIntersection (ElementConstraint (P (FR (RootOnly
                (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "ABC"))))))))))))))

extCon2 :: SubtypeConstraint VisibleString
extCon2 = RootOnly (ComplementSet (EXCEPT (P (FR (NonEmptyExtension
                (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "ABC")))))))
                (UnionSet ( NoUnion (NoIntersection (ElementConstraint (S (SV (VisibleString "0123456789"))))))))))))
\end{code}

{\em encodeUnconstrainedKMS} encodes an unconstrained known-multiplier type value. If the
string is formed of characters from the required type then it calls {\em encodeKMString}. The
test is done by the function {\em isOKString}.

\begin{code}

encodeUnconstrainedKMS :: (Eq a, RS a, Lattice a) => a -> PERMonad ()
encodeUnconstrainedKMS vs
        | isOKString vs top
            = encodeKMString vs
        | otherwise
            = throwError (BoundsError "Invalid value!")


isOKString :: RS a => a -> a -> Bool
isOKString x y = elems (getString x) (getString y)

elems :: Eq a => [a] -> [a] -> Bool
elems xs ys = all (flip elem ys) xs

\end{code}

{\em encodeKMString} encodes a known-multiplier string with unconstrained length and a
permitted-alphabet constraint of the whole type. {\em encodeKMPermAlph} encodes each
character in a string based on the rules specified in X.691 27.5.2 and 27.5.4. Since the
permitted-alphabet constraint is the entire alphabet we use the {\em LatticeMod} entity {\em top}
which represents the greatest element of the particular known-multiplier string type --
the entire alphabet.

\begin{code}

encodeKMString :: (RS a, Lattice a) => a -> PERMonad ()
encodeKMString vs
    = let t = getTop vs
      in {- X691REF: 27.5.7 -}
         encodeWithLength top (encodeKMPermAlph (getString t))  (getString vs)

getTop :: (RS a, Lattice a) => a -> a
getTop m = top

encodeKMPermAlph :: String -> Char -> PERMonad ()
encodeKMPermAlph p c
    = {- X691REF: 27.5.2 and 27.5.4 -}
      let sp  = L.sort p
          lp  = genericLength p
          b   = minExp 2 0 lp
          mp  = maximum p
      in
        if ord mp < 2^b -1
            then {- X691REF: 27.5.4 (a) -}
                 encodeCharInBits lp c
            else {- X691REF: 27.5.4 (b) -}
                 let v = (genericLength . findV c) sp
                     l = fromInteger $ lp-1
                 in toNonNegBinaryInteger v l

minExp :: (Num a, Integral b, Ord a) => a -> b -> a -> b
minExp n e p
    = if n^e < p
        then minExp n (e+1) p
        else e
\end{code}

Each character is encoded by {\em encodeCharInBits}
which encodes the Unicode value of the character in the required number of bits. This is
achieved by converting a character to its Unicode value and then encoding the number as a
constrained integer using {\em toNonNegBinaryInteger}.

\begin{code}

encodeCharInBits :: Integer -> Char -> PERMonad ()
encodeCharInBits i c = toNonNegBinaryInteger (fromInteger . fromIntegral . ord $ c) (fromInteger i)

\end{code}

{\em encodeKMSWithConstraint} calls {\em encodeNonExtConsKMS} if the constraint is not
extensible and the input is valid (for the particular known-multiplier string).
If it is extensible and the input is valid then {\em encodeExtConsKMS} is called. They both take the
effective constraint and actual constraint associated with the type as input.

\begin{code}

encodeKMSWithConstraint :: (Eq a, RS a, Lattice a)
                            => SerialSubtypeConstraints a -> a -> PERMonad ()
encodeKMSWithConstraint cs vs
        | isOKString vs top && not extensible
            = encodeNonExtConsKMS (effectiveCon cs) (actualCon cs) vs
        | isOKString vs top
            =   {- X691REF: 27.4 -}
                encodeExtConsKMS (effectiveCon cs) (actualCon cs) vs
        | otherwise
            = throwError (BoundsError "Invalid value!")
            where
                extensible = eitherExtensible (effectiveCon cs)

effectiveCon :: (RS a, Lattice a, Eq a) => SerialSubtypeConstraints a ->
                Either String (ExtensibleConstraint (ResStringConstraint a IntegerConstraint))
effectiveCon cs
        =   let t = ResStringConstraint top top
                tp = ExtensibleConstraint t t False
                tpp = Right tp
            in
                evaluateConstraint  pvKnownMultiplierElements tpp cs

actualCon :: (RS a, Lattice a, Eq a) => SerialSubtypeConstraints a ->
                Either String (ExtensibleConstraint (ResStringConstraint a ValidIntegerConstraint))
actualCon cs
        =   let t = ResStringConstraint top top
                tp = ExtensibleConstraint t t False
                tpp = Right tp
            in
                evaluateConstraint  pvKnownMultiplierElements tpp cs

\end{code}


{\em encodeNonExtConsKMS} has several cases:
\begin{itemize}
\item
if there is no valid effective constraint (signalled by a {\em Left} value) then an error
indicating this problem is thrown;
\item
if the constraint is empty then an error is thrown since the constraint can never be
satisfied;
\item
if the constraint is a mixture of a size and permitted alphabet constraint and both are
satisfied by the input value then {\em encodeSizeAndPAConsKMS} is called;
\item
if the constraint is only a permitted alphabet constraint then {\em encodePAConsKMS} is
called;
\item
if the constraint is only a size constraint then {\em encodeSizeConsKMS} is called;
\item
if there is no PER-visible constraint (such as an extensible permitted alphabet constraint)
then the value is unconstrained and {\em encodeUnconstrainedLMS} is called;
\item
otherwise the input value does not satisfy the constraint and an error is thrown.
\end{itemize}



\begin{code}

encodeNonExtConsKMS :: (RS a, Eq a, Lattice a) =>
                Either String (ExtensibleConstraint (ResStringConstraint a IntegerConstraint))
                -> Either String (ExtensibleConstraint (ResStringConstraint a ValidIntegerConstraint))
                -> a
                -> PERMonad ()
encodeNonExtConsKMS (Left s) _ _ = throwError (OtherError s)
encodeNonExtConsKMS (Right vsc) (Right ok) vs
     | isEmptyConstraint rc
         = throwError (ConstraintError "Empty constraint")
     | not noSizeConstraint && not noPAConstraint && inPA pac && inSizeRange (getString vs) oksc
         = encodeSizeAndPAConsKMS l u pac vs
     | noSizeConstraint && not noPAConstraint && inPA pac
         = encodePAConsKMS pac vs
     | noPAConstraint && not noSizeConstraint && inSizeRange (getString vs) oksc
         = encodeSizeConsKMS l u vs
     | noPAConstraint && noSizeConstraint
         = encodeUnconstrainedKMS vs
     | otherwise
         = throwError (BoundsError "Value out of range")
           where
                rc = getRootConstraint vsc
                okrc = getRootConstraint ok
                sc = getSizeConstraint rc
                Valid oksc = getSizeConstraint okrc
                pac = getPAConstraint rc
                noSizeConstraint  = sc == top
                noPAConstraint = pac == top
                inPA x  = elems (getString vs) (getString x)
                l = lower sc
                u = upper sc

\end{code}

{\em encodeExtConsKMS} has several cases:
\begin{itemize}
\item
if there is no valid effective constraint (signalled by a {\em Left} value) then an error
indicating this problem is thrown;
\item
if the constraint is empty then an error is thrown since the constraint can never be
satisfied;
\item
if the constraint is a mixture of a size and permitted alphabet constraint and both are
satisfied by the input value then {\em encodeSizeAndPAConsKMS} is called;
\item
if the constraint is only a permitted alphabet constraint then {\em encodePAConsKMS} is
called;
\item
if the constraint is only a size constraint then {\em encodeSizeConsKMS} is called;
\item
otherwise the input value does not satisfy the constraint and an error is thrown.
\end{itemize}

\begin{code}



encodeExtConsKMS :: (RS a, Eq a, Lattice a) =>
              Either String (ExtensibleConstraint (ResStringConstraint a IntegerConstraint))
              -> Either String (ExtensibleConstraint (ResStringConstraint a ValidIntegerConstraint))
              -> a
              -> PERMonad ()
encodeExtConsKMS (Left s) _ _ = throwError (OtherError s)
encodeExtConsKMS (Right vsc) (Right ok) vs
    | isEmptyConstraint rc
           = throwError (ConstraintError "Empty constraint")
    | otherwise
           = do
                catchError (do {- X691REF: 19.4 within root -}
                               encodeConstrainedKMS [0] l u pc vrc vs)
                           (\err -> do {- X691REF: 19.4 not in root -}
                                       encodeNonExtRootConKMS rc ec vrc vec vs)
    where   rc = getRootConstraint vsc
            ec = getExtConstraint vsc
            vrc = getRootConstraint ok
            vec = getExtConstraint ok
            rsc = getSizeConstraint rc
            pc = getPAConstraint rc
            l = lower rsc
            u = upper rsc


encodeConstrainedKMS :: (RS a, Eq a, Lattice a) =>
                        PrefixBit -> InfInteger -> InfInteger -> a -> ResStringConstraint a ValidIntegerConstraint ->
                                a -> PERMonad ()
encodeConstrainedKMS pb l u pc vrc vs
        | noRootSizeConstraint && inPA pc
                    = do tell $ toBitBuilder pb
                         encodePAConsKMS pc vs
        | noRootPAConstraint && inSizeRange (getString vs) vrsc
                    = do tell $ toBitBuilder pb
                         encodeSizeConsKMS l u vs
        | inPA pc && inSizeRange (getString vs) vrsc
                    = do tell $ toBitBuilder pb
                         encodeSizeAndPAConsKMS l u pc vs
       | otherwise
                    = throwError (BoundsError "Value out of range")
       where
            Valid vrsc = getSizeConstraint vrc
            noRootSizeConstraint = l == NegInf && u == PosInf
            noRootPAConstraint = pc == top
            inPA x  = elems (getString vs) (getString x)

{- FIXME check top here -}
encodePAConsKMS :: (RS a) => a -> a -> PERMonad ()
encodePAConsKMS rcs1 rcs2 = encodeWithLength top (encodeKMPermAlph (getString rcs1)) (getString rcs2)


encodeSizeConsKMS :: (RS a, Lattice a) => InfInteger -> InfInteger -> a -> PERMonad ()
encodeSizeConsKMS l u v
    | range == 1 && u < 65536
         = mapM_ (encodeKMPermAlph (getString t)) x
    | u >= 65536
         = encodeKMString v
    | otherwise
         = let Val r = range
               Val v = l
           in do toNonNegBinaryInteger (fromInteger $ genericLength x - v) (fromInteger $ r - 1)
                 mapM_ (encodeKMPermAlph (getString t)) x
          where t = getTop v
                range = u - l + 1
                x = getString v

encodeSizeAndPAConsKMS :: (RS a) => InfInteger -> InfInteger -> a -> a -> PERMonad ()
encodeSizeAndPAConsKMS l u rcs v
    | range == 1 && u < 65536
         = mapM_ (encodeKMPermAlph (getString rcs)) x
    | u >= 65536
         = encodePAConsKMS rcs v
    | otherwise
         = let Val r = range
               Val v = l
           in do toNonNegBinaryInteger (fromInteger $ genericLength x - v) (fromInteger $ r - 1)
                 mapM_ (encodeKMPermAlph (getString rcs)) x
          where
                range = u - l + 1
                x = getString v


encodeNonExtRootConKMS ::  (RS a, Eq a, Lattice a) => ResStringConstraint a IntegerConstraint
                                -> ResStringConstraint a IntegerConstraint
                                -> ResStringConstraint a ValidIntegerConstraint
                                -> ResStringConstraint a ValidIntegerConstraint
                                -> a -> PERMonad ()
encodeNonExtRootConKMS rc ec okrc okec vs
                | (not noRootSizeConstraint && inSizeRange (getString vs) okrsc && noRootPAConstraint && not noExtPAConstraint &&
                   inPA epac) ||
                  (not noRootSizeConstraint && inSizeRange (getString vs) okrsc && not noRootPAConstraint && not noExtPAConstraint &&
                   not (inPA epac) && inPA expac) ||
                  (not noExtSizeConstraint && inSizeRange (getString vs) okesc && not noRootPAConstraint && inPA rpac) ||
                  (not noExtSizeConstraint && inSizeRange (getString vs) okesc && noRootPAConstraint && not noExtPAConstraint &&
                  inPA epac) ||
                  (not noExtSizeConstraint && inSizeRange (getString vs) okesc && not noRootPAConstraint && not noExtPAConstraint &&
                  not (inPA epac) && inPA expac) ||
                  (noRootSizeConstraint && noExtSizeConstraint && ((noRootPAConstraint && not noExtPAConstraint && inPA epac) ||
                  (not noRootPAConstraint && not noExtPAConstraint && not (inPA epac) && inPA expac)))
                     =  do oneBit -- tell [1]
                           encodePAConsKMS top vs
                | noRootPAConstraint && noExtPAConstraint && inSizeRange (getString vs) okesc
                    = do oneBit -- tell [1]
                         encodeKMString vs
                | otherwise
                    = throwError (BoundsError "Value out of range")
            where
                  Valid okesc = getSizeConstraint okec
                  Valid okrsc = getSizeConstraint okrc
                  rsc = getSizeConstraint rc
                  rpac = getPAConstraint rc
                  esc = getSizeConstraint ec
                  epac = getPAConstraint ec
                  concStrs :: RS a => ResStringConstraint a i ->
                                  ResStringConstraint a i -> a
                  concStrs rc ec
                    = let r = (getString . getPAConstraint) rc
                          e = (getString . getPAConstraint) ec
                      in makeString (r++e)
                  expac = concStrs rc ec
                  noRootSizeConstraint  = rsc == top
                  noRootPAConstraint = rpac == top
                  noExtSizeConstraint  = esc == top
                  noExtPAConstraint = epac == top
                  inPA x  = elems (getString vs) (getString x)



\end{code}

 27.5.4 Encoding of a RESTRICTED CHARACTER STRING with a permitted alphabet
 constraint.

\begin{code}


-- The first two cases are described in X.691 27.5.6 and 25.5.7
-- and the last case by 10.9 Note 3.



\end{code}

Clause 38.8 in X680 encoding based on canonical ordering of restricted character string characters

\begin{code}


canEnc b sp [] = return () -- tell []
canEnc b sp (f:r)
        = let v = (genericLength . findV f) sp
           in do toNonNegBinaryInteger v b
                 canEnc b sp r

findV m []  = []
findV m (a:rs)
          = if m == a
                then []
                else a : findV m rs



\end{code}


\end{document}
