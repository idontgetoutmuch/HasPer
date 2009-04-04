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
from2sComplement'} are defined. These are used in the encoding of integers. Note that in Haskell
by default the totality of a module is imported unless explicitly specified within parentheses; and
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
   , from2sComplement'
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
(potentially) serially appolied constraints and will be converted into an effective constraint
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
The input is a constrained type value. The constraint is added to the list of constraint and
the function is called again on the type being constrained. This recursion will continue
until we reach a non-constrained type. The associated list of constraints will then include all
of the seraily applied constraints.
\end{itemize}



\begin{code}
type PERMonad a = ErrorT ASNError (WriterT BitStream Identity) a

type PerEncoding = Either String BitStream
{-
perEncode :: ASNType a -> SerialSubtypeConstraints a -> a -> PERMonad ()
perEncode t cl v = temporaryConvert (encode t cl v)
-}

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
toPER (BITSTRING nbs) x cl = encodeBS nbs cl x
toPER (OCTETSTRING) x cl   = encodeOS cl x
toPER (SEQUENCE s) x cl    = encodeSeq s x -- no PER-Visible constraints
toPER (SEQUENCEOF s) x cl  = encodeSeqOf cl s x
toPER (SET s) x cl         = temporaryConvert (encodeSet s x) -- no PER-Visible constraints
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
\begin{code}

extractValue = runIdentity . runWriterT . runErrorT

extractValue' = runIdentity . runWriterT . runErrorT

completeEncode :: PERMonad () -> PERMonad ()
completeEncode m
    = let (e,v) = extractValue m
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
{- X691REF: 10.2.1 -}   = let (err,enc) = extractValue (completeEncode (encode t [] v))
{- X691REF: 10.2.2 -}     in  encodeOctetsWithLength enc

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

\begin{code}


encodeInt :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
encodeInt [] v = {- X691REF: 12.2.4 -} encodeUnconsInt v
encodeInt cs v = encodeIntWithConstraint parentRoot validPR lc v
   where
      lc         = last cs
      ic         = init cs
      parentRoot :: Either String IntegerConstraint
      parentRoot = lRootIntCons top ic
      validPR :: Either String ValidIntegerConstraint
      validPR    = lRootIntCons top ic

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
and calls {\em encodeExtConsInt} if the constraint is extensible. This function takes five
inputs. The three required for {\em encodeNonExtConsInt} and the two -- actual and effective
-- extension constraints.
\end{itemize}

\begin{code}

encodeIntWithConstraint :: Either String IntegerConstraint -> Either String ValidIntegerConstraint
                  -> SubtypeConstraint InfInteger -> InfInteger -> PERMonad ()
encodeIntWithConstraint pr vpr lc v
    = if (not extensible)
        then {- X691REF: 12.2 -} encodeNonExtConsInt validRootCon effRootCon v
        else {- X691REF: 12.1 -} encodeExtConsInt validRootCon validExtCon effRootCon effExtCon v
      where
        (effExtCon,extensible)  = lApplyExt pr lc
        effRootCon              = lEvalC lc pr
        (validExtCon,b2)        = lApplyExt vpr lc
        validRootCon            = lEvalC lc vpr

\end{code}



The functions {\em isNonEmptyConstraint} and {\em isEmptyConstraint} simply test whether the
combination of PER-visible constraints associated with an integer type results in an actual
constraint or no constraint. For example, the intersection of two mutually exclusive
constraints results in no constraint. This will then mean that their can be no valid values
and an error must be reported.

The function {\em inRange} simply tests with a value sits within the constraint. It is tested
against the actual constraint and not agianst the effective constraint which is used for
encoding.

\begin{code}

isNonEmptyConstraint,isEmptyConstraint :: (Eq t, Lattice t) => t -> Bool
isNonEmptyConstraint x  = x /= bottom
isEmptyConstraint       = (not . isNonEmptyConstraint)

inRange :: InfInteger -> ValidIntegerConstraint -> Bool
inRange _ (Valid [])       = False
inRange n (Valid (x:rs))   = n >= (lower x) && n <= (upper x) || inRange n (Valid rs)

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
encodeNonExtConsInt :: Either String ValidIntegerConstraint
                     -> Either String IntegerConstraint
                     -> InfInteger
                     -> PERMonad ()
encodeNonExtConsInt (Right validRootCon) (Right effRootCon) n
    | isEmptyConstraint effRootCon
         = throwError (ConstraintError "Empty constraint")
    | isNonEmptyConstraint effRootCon && inRange n validRootCon
         = case constraintType effRootCon of
                 UnConstrained
                        -> {- X691REF: 12.2.4 -} encodeUnconsInt n
                 SemiConstrained
                        -> {- X691REF: 12.2.3 -} encodeSemiConsInt n rootLower
                 Constrained
                        -> {- X691REF: 12.2.2 -} encodeConstrainedInt ((n - rootLower), rootUpper - rootLower)
    | otherwise
        = throwError (BoundsError "Value out of range")
          where
          rootLower          = lower effRootCon
          rootUpper          = upper effRootCon

\end{code}


{\em encodeExtConsInt} is similar to {\em encodeNonExtConsInt}. It has the five cases
described for {\em encodeNonExtConsInt} -- where any encoding is prefixed by the bit 0 --
plus the case when the value satisfies the constraint
but is not within the extension root. In this case the value is encoded as an unconstrained
integer using {\em encodeUnconsInt} prefixed by the bit 1.

\begin{code}

encodeExtConsInt :: Either String ValidIntegerConstraint
                  -> Either String ValidIntegerConstraint
                  -> Either String IntegerConstraint
                  -> Either String IntegerConstraint
                  -> InfInteger
                  -> PERMonad ()
encodeExtConsInt (Right validRootCon) (Right validExtCon)
                 (Right effRootCon) (Right effExtCon) n
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
                         rootLower          = lower effRootCon
                         rootUpper          = upper effRootCon


\end{code}

{\em encodeSemiConsInt} encodes a semi-constrained integer. The difference between the value and the
lower bound is encoded as a non-negative-binary-integer in the mininum number of octets using
{\em encodeNonNegBinaryIntInOctets}. This is prefixed by an encoding of the length of the
octeys using {\em encodeOctetsWithLength}.

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
unconstrained length. {\em encodeBitsWithLength does} the same except
for a collection of bits.

\begin{code}

encodeOctetsWithLength :: [Int] -> PERMonad ()
encodeOctetsWithLength = encodeWithLength (mapM_ tell . id) . groupBy 8


encodeBitsWithLength :: [Int] -> PERMonad ()
encodeBitsWithLength = encodeWithLength (tell.id)

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


\section{Length Determinants}

10.9 General rules for encoding a length determinant
10.9.4, 10.9.4.2 and 10.9.3.4 to 10.9.3.8.4.

{\em encodeWithLength} takes a list of values (could be bits, octets or
any ASN.1 type), and groups them first in 16k batches, and then in
batches of 4. The input value-encoding function is then supplied as
an input to the function {\em addUncLen} which manages the interleaving of
length and value encodings -- it encodes the length and values of
each batch and concatenates their resulting bitstreams together.
Note the values are encoded using the input function.

\begin{code}

encodeWithLength :: ([t] -> PERMonad ()) -> [t] -> PERMonad ()
encodeWithLength fun = addUncLen fun . groupBy 4 . groupBy (16*(2^10))

groupBy :: Int -> [t] -> [[t]]
groupBy n =
   unfoldr k
      where
         k [] = Nothing
         k p = Just (splitAt n p)

\end{code}

{\em addUncLen} is a higher order function which encodes a value with an unconstrained
length i.e. it either has no upper bound on the size of the value,
or the upper bound is at least 64k. The inputs are the value encoding
function and the value represented as a collection of 4*16k
blocks.

{\em lastLen} encodes the length remainder modulo 16k and {\em blocklen}
encodes the length of a block (1 to 4).

\begin{code}

addUncLen :: ([b] -> PERMonad ()) -> [[[b]]] -> PERMonad ()
addUncLen encFun [] = lastLen k16 0
addUncLen encFun (x:xs)
    | l == 4 && last16 == k16
        = do blockLen 4 63
             mapM_ encFun x
             addUncLen encFun xs
    | l == 1 && last16 < k16
        = do lastLen k16 ((genericLength . head) x)
             encFun (head x)
    | otherwise
        = if last16 == k16
             then do blockLen l 63
                     mapM_ encFun x
                     lastLen k16 0
             else do blockLen (l-1) 63
                     mapM_ encFun (init x)
                     lastLen k16 ((genericLength.last) x)
                     encFun (last x)
    where
        l      = genericLength x
        last16 = (genericLength . last) x

k16 :: InfInteger
k16    = 16*(2^10)


lastLen :: InfInteger -> InfInteger -> PERMonad ()
lastLen r n
   | n <= 127
        = do tell [0]
             encodeConstrainedInt (n, 127)
   | n < r
        = do tell [1]
             tell [0]
             encodeConstrainedInt (n, (r-1))
   | otherwise
        = throwError (BoundsError "Length is out of range.")

blockLen :: InfInteger -> InfInteger -> PERMonad ()
blockLen x y
    = do tell [1]
         tell [1]
         encodeConstrainedInt (x,y)

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
   | otherwise = encodeNonNegBinaryIntInOctets (fromInteger $ 2^p + n)
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

 10.6 Encoding as a normally small non-negative whole number

\begin{code}

encodeNSNNInt :: Integer -> Integer -> PERMonad ()
encodeNSNNInt n lb
    = if n <= 63
        then do tell [0]
                encodeConstrainedInt (fromInteger n, fromInteger 63)
        else do tell [1]
                encodeSemiConsInt (fromInteger n) (fromInteger lb)

\end{code}


\section{ENCODING THE ENUMERATED TYPE}

There are three cases to deal with:

\begin{enumerate}

\item
There is no extension marker. The enumerations are indexed
based on their (explicit or implicit) values. Thus each
enumeration without an explicit value, is given a value that is not
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

encodeEnum :: Enumerate a -> ExactlyOne a SelectionMade -> PERMonad ()
encodeEnum e x
    = let (b,inds) = assignIndex e
          no = genericLength inds
      in
        encodeEnumAux b no inds e x

encodeEnumAux :: Bool -> Integer -> [Integer] -> Enumerate a -> ExactlyOne a n
                 -> PERMonad ()
encodeEnumAux b no (f:r) (AddEnumeration  _ es) (AddAValue a rest)
    = if not b
        then encodeConstrainedInt (fromInteger f, fromInteger (no-1))
        else do tell [0]
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
    = do tell [1]
         encodeNSNNInt i 0
encodeEnumExtAux i l (AddEnumeration  _ es) (AddNoValue a rest)
    = encodeEnumExtAux (i+1) l es rest
encodeEnumExtAux i l _ _ = throwError (OtherError "No enumerated extension value!")

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

\section{ENCODING THE BIT STRING TYPE}

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

inSizeRange _  [] = False
inSizeRange p qs = inSizeRangeAux qs
   where
      l = genericLength p
      inSizeRangeAux (x:rs) =
         l >= (lower x) && l <= (upper x) || inSizeRangeAux rs

\end{code}

\subsection{Original Code}

\begin{code}

encodeBS :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PERMonad ()
encodeBS nbs [] x = encodeBSNoSz nbs x
encodeBS nbs cl x = encodeBSSz nbs cl x


encodeBSSz :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PERMonad ()
encodeBSSz nbs cl xs = lEncValidBS nbs (effBSCon cl) (validBSCon cl) xs

effBSCon ::[SubtypeConstraint BitString] -> Either String (ExtBS (ConType IntegerConstraint))
effBSCon cs = lSerialEffCons lBSConE top cs


validBSCon :: [SubtypeConstraint BitString] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validBSCon cs = lSerialEffCons lBSConE top cs


lEncValidBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> BitString -> PERMonad ()
lEncValidBS nbs m@(Right c) n v
    = if extensibleBS c
            then lEncExtBS nbs m n v
            else lEncNonExtBS nbs m n v
lEncValidBS nbs (Left s) _ _ = throwError (ConstraintError s)


lEncNonExtBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> BitString
                -> PERMonad ()
lEncNonExtBS nbs (Right vsc) (Right ok) (BitString vs)
    | emptyConstraint
           = throwError (ConstraintError "Empty constraint")
    | null nbs && inSizeRange okrc || (not . null) nbs
           = let (_,bs) = extractValue (bsCode nbs rc vs)
              in  tell bs
    | otherwise
           = throwError (BoundsError "Value out of range")
             where
                rc = conType . getBSRC $ vsc
                okrc :: [IntegerConstraint]
                Valid okrc = conType . getBSRC $ ok
                emptyConstraint = rc == bottom
                inSizeRange []      = False
                inSizeRange (x:rs)
                    = let l = genericLength vs
                      in l >= (lower x) && l <= (upper x) || inSizeRange rs



lEncExtBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> BitString
                -> PERMonad()
lEncExtBS nbs (Right vsc) (Right ok) (BitString vs)
    =   let rc = conType . getBSRC $ vsc
            Valid okrc = conType . getBSRC $ ok
            ec = conType . getBSEC $ vsc
            Valid okec = conType . getBSEC $ ok
            emptyConstraint = rc == bottom && ec == bottom
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength vs
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            foobar
                | emptyConstraint
                    = throwError (ConstraintError "Empty constraint")
                | inSizeRange okrc
                    = let (_,bs) = extractValue $ bsCode nbs rc vs
                      in do tell [0]
                            tell bs
                | inSizeRange okec
                     = let (_,bs) = extractValue $ bsExtCode nbs rc ec vs
                       in do tell [1]
                             tell bs
                | otherwise
                    = throwError (BoundsError "Value out of range")
         in foobar


bsCode :: NamedBits -> IntegerConstraint -> BitStream -> PERMonad ()
bsCode nbs rc xs
      =  let l  = lower rc
             u  = upper rc
             exs = if (not.null) nbs then editBS l u xs
                     else tell xs
         in
             if u == 0
             then tell []
             else if u == l && u <= 65536
                       then exs
                       else if u <= 65536
                            then let Val ub = u
                                     Val lb = l
                                     (_,ls) = extractValue $ exs
                                 in do encodeConstrainedInt (fromInteger (genericLength ls - lb), u-l)
                                       tell ls
                            else let
                                    (_,ls) = extractValue $ exs
                                 in encodeBitsWithLength ls

bsExtCode :: NamedBits -> IntegerConstraint -> IntegerConstraint -> BitStream -> PERMonad ()
bsExtCode nbs rc ec xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
          exs = if (not.null) nbs then editBS l u xs
                     else tell xs
      in
          if u <= 65536
             then let Val ub = u
                      Val lb = l
                      (_,ls) = extractValue $ exs
                  in do
                        encodeConstrainedInt (fromInteger (genericLength ls -lb), u-l)
                        tell ls
             else let (_,ls) = extractValue $ exs
                  in encodeBitsWithLength ls


editBS :: InfInteger -> InfInteger -> BitStream -> PERMonad ()
editBS l u xs
    = let lxs = genericLength xs
      in if lxs < l
        then add0s (l-lxs) xs
        else
            if lxs > u
             then rem0s (lxs-u) xs
             else tell xs

add0s :: InfInteger -> BitStream -> PERMonad ()
add0s (Val n) xs = do
                     tell xs
                     tell $ take (fromInteger n) [0,0..]
add0s _ _        = throwError (OtherError "Invalid number input -- MIN or MAX.")

rem0s :: InfInteger -> BitStream -> PERMonad ()
rem0s (Val (n+1)) xs
    = if last xs == 0
           then rem0s (Val n) (init xs)
           else throwError (OtherError "Last value is not 0")
rem0s (Val 0) xs = tell xs
rem0s _ _  = throwError (OtherError "Cannot remove a negative, MIN or MAX number of 0s.")

\end{code}


\begin{code}
encodeBSNoSz :: NamedBits -> BitString -> PERMonad ()
encodeBSNoSz nbs (BitString [])
    = tell []
encodeBSNoSz nbs (BitString bs)
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

\section{ENCODING THE OCTETSTRING TYPE}

\begin{code}

encodeOS :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOS [] x = encodeOSNoSz x
encodeOS cl x = encodeOSSz cl x

\end{code}

encodeOctS encodes an unconstrained SEQUENCEOF value.

\begin{code}

encodeOSNoSz :: OctetString -> PERMonad ()
encodeOSNoSz (OctetString xs)
    = let foo x = encodeConstrainedInt ((fromIntegral x),255)
      in
        encodeWithLength (mapM_ foo) xs


encodeOSSz :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOSSz cl xs = lEncValidOS (effOSCon cl) (validOSCon cl) xs

effOSCon ::[SubtypeConstraint OctetString] -> Either String (ExtBS (ConType IntegerConstraint))
effOSCon cs = lSerialEffCons lOSConE top cs


validOSCon :: [SubtypeConstraint OctetString] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validOSCon cs = lSerialEffCons lOSConE top cs


lEncValidOS :: Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> OctetString -> PERMonad ()
lEncValidOS m@(Right vsc) n v
    = if extensibleBS vsc
            then lEncExtOS m n v
            else lEncNonExtOS m n v
lEncValidOS (Left s) _ _
    = throwError (ConstraintError s)



lEncNonExtOS :: Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> OctetString
                -> PERMonad ()
lEncNonExtOS (Right vsc) (Right ok) (OctetString vs)
        | isEmptyConstraint rc
              = throwError (ConstraintError "Empty constraint")
        | inSizeRange vs okrc
             = let (_,bs) = extractValue $ osCode rc vs
               in tell bs
        | otherwise
             = throwError (BoundsError "Value out of range")
               where
                rc = conType . getBSRC $ vsc
                Valid okrc = conType . getBSRC $ ok


lEncExtOS :: Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> OctetString
                -> PERMonad ()
lEncExtOS (Right vsc) (Right ok) (OctetString vs)
         | isEmptyConstraint rc
               = throwError (ConstraintError "Empty constraint")
         | inSizeRange vs okrc
               = let (_,bs) = extractValue $ osCode rc vs
                 in do tell [0]
                       tell bs
                | inSizeRange vs okec
                    = let (_,bs) = extractValue $ osExtCode rc ec vs
                      in do tell [1]
                            tell bs
                | otherwise
                    = throwError (BoundsError "Value out of range")
                      where
                        rc = conType . getBSRC $ vsc
                        Valid okrc = conType . getBSRC $ ok
                        ec = conType . getBSEC $ vsc
                        Valid okec = conType . getBSEC $ ok


osCode :: IntegerConstraint -> [Octet] -> PERMonad ()
osCode rc xs
      =  let l  = lower rc
             u  = upper rc
             octetToBits x = encodeConstrainedInt ((fromIntegral x),255)
             octetsToBits  = mapM_ octetToBits
         in
             if u == 0
             then tell []
             else if u == l && u <= 65536
                       then octetsToBits xs
                       else if u <= 65536
                            then let Val ub = u
                                     Val lb = l
                                 in do
                                     encodeConstrainedInt (((fromInteger.genericLength) xs -l),
                                                                    (u-l))
                                     octetsToBits xs
                            else encodeWithLength octetsToBits xs

osExtCode :: IntegerConstraint -> IntegerConstraint -> [Octet] -> PERMonad ()
osExtCode rc ec xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
          octetToBits x = encodeConstrainedInt ((fromIntegral x),255)
          octetsToBits  = mapM_ octetToBits
      in if u <= 65536
         then let Val ub = u
                  Val lb = l
              in do
                   encodeConstrainedInt ((fromInteger.genericLength) xs - l, (u-l))
                   octetsToBits xs
         else encodeWithLength octetsToBits xs

\end{code}

\section{ENCODING THE SEQUENCE TYPE}

\begin{code}

encodeSeq :: Sequence a -> a -> PERMonad ()
encodeSeq s x
    = case encodeSeqAux ([],[]) ([],[]) s x
        of Right ((rp,rb),(ap,ab))  ->
                if null ap
                    then
                     do mapM_ tell rp
                        mapM_ tell rb
                        mapM_ tell ap
                        mapM_ tell ab
                    else
                     do mapM_ tell rp
                        mapM_ tell rb
                        lengthAdds ap
                        mapM_ tell ab
           Left s ->
                throwError (OtherError s)

\end{code}

I DON'T THINK THAT THE ELSE CASE IS FRAGMENTING CORRECTLY

18.8 A length determinant of the number of extension additions is added if
the sequence has any extension additions declared. This is encoded as a normally
small length (10.9.3.4)

\begin{code}

lengthAdds ap
    = let la = genericLength ap
       in if la <= 63
        then do tell [0]
                encodeConstrainedInt (la-1, 63)
                mapM_ tell ap
        else do tell [1]
                encodeOctetsWithLength (encodeNonNegBinaryIntInOctets la)
                mapM_ tell ap

\end{code}

encodeSeqAux is the auxillary function for encodeSeq. When
encoding a sequence, one has to both encode each component and
produce a preamble which indicates the presence or absence of an
optional or default value. The first list in the result is the
preamble. The constructor ExtensionMarker indicates the sequence is
extensible, and the coding responsibility is passed to
encodeExtSeqAux (where the values are encoded as an open type).
Note that if another ExtensionMarker occurs then reponsibility returns
to encodeSeqAux since this is the 2 extension marker case
(and what follows is in the extension root).

encodeCO implments the encoding of a COMPONENTS OF component of a
sequence. The (non-extension) components of the referenced
sequence are embedded in the parent sequence and are enocoded as
if components of this sequence.

\begin{code}

encodeSeqAux :: ([BitStream],[BitStream]) -> ([BitStream],[BitStream]) -> Sequence a -> a ->
      Either String (([BitStream],[BitStream]),([BitStream],[BitStream]))
encodeSeqAux (ap,ab) (rp,rb) EmptySequence Empty
    = if ((not.null) (concat ab))
        then return (([1]:reverse rp,reverse rb),(reverse ap,reverse ab))
        else return ((reverse rp,reverse rb),(reverse ap, reverse ab))
encodeSeqAux (ap,ab) (rp,rb) (ExtensionMarker as) xs
    = encodeExtSeqAux (ap,ab) (rp,rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs) -- typically a reference
    = do (p,b) <- encodeCO ([],[]) s x
         encodeSeqAux (ap,ab) (p ++ rp,b ++ rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf (ReferencedType n t)) as) (x:*:xs) -- typically a reference
    = encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf (ConstrainedType t c)) as) (x:*:xs) -- typically a reference
    = encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf t) as) (x:*:xs)
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ComponentsOf _) as) (x:*:xs)
    = throwError "COMPONENTS OF can only be applied to a SEQUENCE."
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeSeqAux (ap,ab) ([]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeSeqAux (ap,ab) ([]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeSeqAux (ap,ab) ([1]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeSeqAux (ap,ab) ([1]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (ExtensionAdditionGroup _ _ _) _
    = throwError "Impossible case: Extension Addition Groups only appear within an extension"

encodeCO :: ([BitStream],[BitStream]) -> Sequence a -> a -> Either String (([BitStream],[BitStream]))
encodeCO (rp,rb) EmptySequence _
    = return (rp,rb)
encodeCO (rp,rb) (ExtensionMarker as) xs
    = encodeExtCO (rp,rb) as xs
encodeCO (rp,rb) (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do (p,b) <- encodeCO ([],[]) s x
         encodeCO (p ++ rp,b ++ rb) as xs
encodeCO (rp,rb) (AddComponent (ComponentsOf _) as) (x:*:xs)
    = throwError "COMPONENTS OF can only be applied to a SEQUENCE"
encodeCO (rp,rb) (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do (err,bts) <- return (extractValue (encode a [] x))
         encodeCO ([]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeCO ([]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do (err,bts) <- return (extractValue (encode a [] x))
         encodeCO ([]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeCO ([1]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        (err,bts) <- return (extractValue (encode a [] x))
        encodeCO ([1]:rp,bts:rb) as xs
encodeCO (rp,rb) (ExtensionAdditionGroup _ _ _) _
    = throwError "Impossible case: Extension Addition Groups only appear in an extension."


-- Only the root component list of the COMPONENTS OF type is inlcuded.
encodeExtCO :: ([BitStream],[BitStream]) -> Sequence a -> a -> Either String (([BitStream],[BitStream]))
encodeExtCO (rp,rb) EmptySequence _
    = return (rp,rb)
encodeExtCO (rp,rb) (ExtensionMarker as) xs
    = encodeCO (rp,rb) as xs
encodeExtCO (rp,rb) (AddComponent _ as) (_:*:xs)
    = encodeExtCO (rp,rb) as xs
encodeExtCO (rp,rb) (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = encodeExtCO (rp,rb) as xs
\end{code}

encodeExtSeqAux adds the encoding of any extension additions to
the encoding of the extension root. If an addition is present a
1 is added to a bitstream prefix and the value is encoded as an
open type (using encodeOpen). If an addition is not present then a
0 is added to the prefix.

\begin{code}

encodeExtSeqAux :: ([BitStream],[BitStream]) -> ([BitStream], [BitStream]) -> Sequence a -> a ->
    Either String (([BitStream],[BitStream]),([BitStream],[BitStream]))
encodeExtSeqAux (ap,ab) (rp,rb) EmptySequence _
    = if (length . filter (==[1])) ap > 0
                then  return (([1]:reverse rp,reverse rb),(reverse ap,reverse ab))
                else  return (([0]:reverse rp,reverse rb),(reverse ap,reverse ab))
encodeExtSeqAux extAdds extRoot (ExtensionMarker as) xs =
   encodeSeqAux extAdds extRoot as xs
encodeExtSeqAux (ap,ab) (rp,rb) (ExtensionAdditionGroup _ a as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do (err,bts) <- return (runIdentity (runWriterT (runErrorT
                            (encodeOpen (BuiltinType (SEQUENCE a)) x))))
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do (err,bts) <- return (runIdentity (runWriterT (runErrorT (encodeOpen a x))))
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do (err,bts) <- return (runIdentity (runWriterT (runErrorT (encodeOpen a x))))
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
   = do (err,bts) <- return (runIdentity (runWriterT (runErrorT (encodeOpen a x))))
        encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) _ _
    = throwError "Impossible case for extension addition."


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
     y <= 64*(2^10) = f t xs
   | ub == maxBound = encodeLargeLengthDeterminant f t xs {- FIXME: A word of explanation as to why
                                                             we test this here - it's because after
                                                             here we know y is defined. -}
   | y <= 64*(2^10) {- 10.9.1 -}
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
      in  mAddUncLen fun ls


mAddUncLen :: ([[b]] -> PERMonad ()) -> [[[b]]] -> PERMonad ()
mAddUncLen encFun [] = lastLen k16 0
mAddUncLen encFun (x:xs)
    | l == 4 && last16 == k16
        = do
            blockLen 4 63
            encFun x
            mAddUncLen encFun xs
    | l == 1 && last16 < k16
        = do
            lastLen k16 ((genericLength . head) x)
            encFun ([head x])
    | last16 == k16
        = do
            blockLen l 63
            encFun x
            lastLen k16 0
    | otherwise
        = do
            blockLen (l-1) 63
            encFun (init x)
            lastLen k16 ((genericLength.last) x)
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
                            then let Val ub = u
                                     Val lb = l
                                 in do
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
                            then let Val ub = u
                                     Val lb = l
                                 in do
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

encodeSet :: Sequence a -> a -> PerEncoding
encodeSet s x
    =   do
            ((rp,rb),(ap,ab)) <- encodeSeqAux ([],[]) ([],[]) s x
            let ts  = getTags s
                ps  = zip ts rb
                pps = zip rp ps
                os  = mergesort setPred pps
                pr  = concat (map fst os)
                en  = concat (map (snd . snd) os)
            return (pr ++ en ++ concat ap ++ concat ab)

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
          gl = genericLength (getString t)
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
          l = genericLength (getString t)
      in
         encodeWithLength (encSF (getString t))  (getString vs)

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
encodeRCSF rcs1 rcs2 = encodeWithLength (encSF (getString rcs1)) (getString rcs2)


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

\end{code}

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



\section{Decoding Length Determinants}

This function decodes the length determinant as defined in 10.9.
It does not currently cover 10.9.3.4: the determinant being a normally small length.

Note that it assumes that the ASN.1 type makes semantic sense.
For example, if the upper bound of the size constraint ("ub") is 0 and the
lower bound ("lb") is negative, then the result is undefined.




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



This function decodes the length determinant for unconstrained length or large "ub".
See 10.9.4 and 10.9.3.4 -- 10.9.3.8.4 for further details. Note that we don't currently
cover 10.9.3.4!!! It does so by taking a function which itself takes an iteration count,
an ASN.1 type and returns a (monadic) list of decoded values which may or may not be
values of the ASN.1 type.


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



\section {INTEGER Decoding}

Constrained {\em INTEGER}s are encoded as non-negative binary in
the least number of bits
unless the range is 1 (in which case the answer is the lower and upper bound) --- see Note 2 in Clause 12.

Semi-constrained and unconstrained {\em INTEGER}s are encoded in a list of chunks of
8 bits (octets) as non-negative binary or as two's complement respectively with a
\lq\lq large\rq\rq\ length determinant (as there are no constraints on the length
determinant itself in this particular case).

\begin{code}

data ASNError =
     ConstraintError String
   | BoundsError     String
   | DecodeError     String
   | ExtensionError  String
   | OtherError      String
      deriving Show

instance Error ASNError where
   noMsg = OtherError "The impossible happened"

\end{code}

decodeInt3 :: ASNMonadTrans t => [ElementSetSpecs InfInteger] -> t BG.BitGet InfInteger
decodeInt3 [] =
   lDecConsInt3 (return bottom) undefined (return bottom)
decodeInt3 cs =
   lDecConsInt3 (errorize effRoot) isExtensible (errorize effExt)
   where
      lc                    = last cs
      ic                    = init cs
      parentRoot            = lRootIntCons top ic
      (effExt,isExtensible) = lApplyExt parentRoot lc
      effRoot               = lEvalC lc parentRoot

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
          numOfRootBits          = genericLength (encodeConstrainedInt (rootRange - 1, rootRange - 1))
          numOfExtensionBits     = genericLength (encodeConstrainedInt (extensionRange - 1, extensionRange - 1))
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




\section{SEQUENCE Decoding}



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





forget :: (MonadTrans t, MonadError [Char] (t BG.BitGet)) => Either String (t BG.BitGet a) -> t BG.BitGet a
forget (Left e) = throwError e
forget (Right x) = x

swap :: (Functor m, Monad m) => Either String (m a) -> m (Either String a)
swap (Left s) = return (Left s)
swap (Right x) = fmap Right x



\section{SEQUENCE OF Decoding}


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



\subsection{BIT STRING --- Clause 15}

{\em BIT STRING}s are encoded with a length determinant but the type
is immaterial hence we use $\bottom$ as the type argument to
{\em decodeLengthDeterminant}; the (function) argument to
decode the individual components merely takes 1 bit at a time.

The above may now be rubbish and the code below could well be
highly inefficient.


class (MonadError ASNError (t BG.BitGet), MonadTrans t) => ASNMonadTrans t

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





\section{Bibliography}

\bibliographystyle{plainnat}

\bibliography{3gpp,ASN1}

\section{Appendix: Tests}

%include TestCTR.lhs

\end{document}
