v v v v v v v
*************

^ ^ ^ ^ ^ ^ ^
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

\section{Encoding and Decoding}

The encoding is for UNALIGNED PER

%if False

\begin{code}

{-# OPTIONS_GHC -XMultiParamTypeClasses -XGADTs -XTypeOperators
                -XEmptyDataDecls -XFlexibleInstances -XFlexibleContexts
                -fwarn-unused-imports -fwarn-incomplete-patterns
#-}

\end{code}

%endif

\begin{code}

module PER where

import ASNTYPE
import Data.List hiding (groupBy)
import Data.Char
import Control.Monad.Error
import Control.Monad.Identity
import qualified Data.ByteString as B
import qualified Data.Binary.Strict.BitGet as BG
import qualified Data.Binary.BitPut as BP
import Language.ASN1.PER.Integer
   ( fromNonNegativeBinaryInteger'
   , from2sComplement'
   )
import Data.Int
import Data.Maybe
import LatticeMod
import ConstraintGeneration

\end{code}




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

type PerEncoding = Either String BitStream
type PEREncoding = Either String BP.BitPut

perEncode :: ASNType a -> SerialSubtypeConstraints a -> a -> PEREncoding
perEncode t cl v
    = do
        bts <- lEncode t cl v
        return (bitPutify bts)

bitPutify :: BitStream -> BP.BitPut
bitPutify = mapM_ (BP.putNBits 1)

lEncode :: ASNType a -> SerialSubtypeConstraints a -> a -> PerEncoding
lEncode (BuiltinType t) cl v       = toPER t v cl
lEncode (ReferencedType r t) cl v  = lEncode t cl v
lEncode (ConstrainedType t c) cl v = lEncode t (c:cl) v

\end{code}

need to deal with per-visible constraint list here.
generate effective root and effective extension here.

\begin{code}

toPER :: ASNBuiltin a -> a -> SerialSubtypeConstraints a -> PerEncoding
toPER NULL _ _             = Right []
toPER INTEGER x cl         = lEncodeInt cl x
toPER VISIBLESTRING x cl   = lEncodeRCS cl x
toPER PRINTABLESTRING x cl = lEncodeRCS cl x
toPER NUMERICSTRING x cl   = lEncodeRCS cl x
toPER IA5STRING x cl       = lEncodeRCS cl x
toPER BMPSTRING x cl       = lEncodeRCS cl x
toPER UNIVERSALSTRING x cl = lEncodeRCS cl x
toPER BOOLEAN x cl         = lEncodeBool cl x
toPER (ENUMERATED e) x cl  = lEncodeEnum e x -- no PER-Visible constraints
toPER (BITSTRING nbs) x cl = lEncodeBS nbs cl x
toPER (OCTETSTRING) x cl   = lEncodeOS cl x
toPER (SEQUENCE s) x cl    = lEncodeSeq s x -- no PER-Visible constraints
toPER (SEQUENCEOF s) x cl  = lEncodeSeqOf cl s x
toPER (SET s) x cl         = lEncodeSet s x -- no PER-Visible constraints
toPER (CHOICE c) x cl      = lEncodeChoice c x -- no PER-visible constraints
toPER (SETOF s) x cl       = lEncodeSeqOf cl s x -- no PER-visible constraints
toPER (TAGGED tag t) x cl  = lEncode t cl x

\end{code}

\section{ENCODING AN OPEN TYPE FIELD}

lEncodeOpen encodes an open type value. That is:
i. the value is encoded as ususal;
ii. it is padded at the end with 0s so that it has a octet-multiple length; and
iii. its length is added as a prefix using the fragmentation rules (10.9)
The first case is required since an extension addition group is
encoded as an open type sequence and lEncodeOpen is always called by
toPer on an extension component (avoids encoding it as an open
type open type sequence!)

\begin{code}

lEncodeOpen :: ASNType a -> a -> PerEncoding
lEncodeOpen t v
   = do enc <- lEncode t [] v
        pad <- padding enc
        return (encodeOctetsWithLength pad)

padding enc
    = let le  = length enc
          bts = le `mod` 8
          pad = if bts == 0
                   then enc
                   else enc ++ take (8-bts) [0,0..]
      in return pad

\end{code}


\section{ENCODING THE BOOLEAN TYPE}

\begin{code}

lEncodeBool :: [SubtypeConstraint Bool] -> Bool -> PerEncoding
lEncodeBool t True = return ( [1])
lEncodeBool t _    = return ( [0])

\end{code}

\section{ENCODING THE INTEGER TYPE}

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

myEncodeUInt (Val x)
    = (encodeUInt . fromIntegral) x

lEncodeInt :: [SubtypeConstraint InfInteger] -> InfInteger -> PerEncoding
lEncodeInt [] v = return (myEncodeUInt v)
lEncodeInt cs v =
   lEitherTest parentRoot validPR lc v
   where
      lc         = last cs
      ic         = init cs
      parentRoot :: Either String IntegerConstraint
      parentRoot = lRootIntCons top ic
      validPR :: Either String ValidIntegerConstraint
      validPR    = lRootIntCons top ic



lEitherTest :: Either String IntegerConstraint -> Either String ValidIntegerConstraint
               -> SubtypeConstraint InfInteger -> InfInteger -> PerEncoding
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

lEncConsInt :: (Eq t, Lattice t) =>
               Either String ValidIntegerConstraint
               -> Either String ValidIntegerConstraint
               -> Either String IntegerConstraint
               -> Either String t
               -> Bool
               -> InfInteger
               -> PerEncoding
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

lEncExtConsInt :: (Eq t, Lattice t) =>
                  Either String ValidIntegerConstraint
                  -> Either String ValidIntegerConstraint
                  -> Either String IntegerConstraint
                  -> Either String t
                  -> InfInteger
                  -> PerEncoding
lEncExtConsInt realRC realEC effRC effEC n@(Val v) =
   do
      Valid rrc <- realRC
      Valid rec <- realEC
      erc <- effRC
      eec <- effEC
      let isNonEmptyEC           = eec /= bottom
          isNonEmptyRC           = erc /= bottom
          emptyConstraint        = (not isNonEmptyRC) && (not isNonEmptyEC)
          inRange []             = False
          inRange (x:rs)         = n >= (lower x) && n <= (upper x) || inRange rs
          unconstrained x        = (lower x) == minBound
          semiconstrained x      = (upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          Val rootLower              = lower erc
          Val rootUpper              = upper erc
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rrc
                  = return $ do
                                case constraintType erc of
                                   UnConstrained ->
                                        0:encodeUInt (fromIntegral v)
                                   SemiConstrained ->
                                        0:encodeSCInt (fromIntegral v) rootLower
                                   Constrained ->
                                        0:encodeNNBIntBits (fromIntegral (v - rootLower), fromIntegral (rootUpper - rootLower))
             | isNonEmptyEC && inRange rec
                  = return (1:encodeUInt (fromIntegral v))
             | otherwise
                  = throwError "Value out of range"
      foobar
lEncExtConsInt realRC realEC effRC effEC v = throwError "Cannot encode MAX or MIN."

lEncNonExtConsInt :: Either String ValidIntegerConstraint
                     -> Either String IntegerConstraint
                     -> InfInteger
                     -> PerEncoding
lEncNonExtConsInt realRC effRC n@(Val v) =
   do Valid rrc <- realRC
      erc <- effRC
      let isNonEmptyRC           = erc /= bottom
          emptyConstraint        = not isNonEmptyRC
          inRange []             = False
          inRange (x:rs)         = n >= (lower x) && n <= (upper x) || inRange rs
          unconstrained x        = (lower x) == minBound
          semiconstrained x      = (upper x) == maxBound
          constrained x          = not (unconstrained x) && not (semiconstrained x)
          constraintType x
             | unconstrained x   = UnConstrained
             | semiconstrained x = SemiConstrained
             | otherwise         = Constrained
          Val rootLower          = lower erc
          Val rootUpper          = upper erc
          foobar
             | emptyConstraint
                  = throwError "Empty constraint"
             | isNonEmptyRC && inRange rrc
                  = return $ do
                       case constraintType erc of
                                   UnConstrained ->
                                      encodeUInt (fromIntegral v)
                                   SemiConstrained ->
                                      encodeSCInt (fromIntegral v) rootLower
                                   Constrained ->
                                      encodeNNBIntBits (fromIntegral (v - rootLower), fromIntegral (rootUpper - rootLower))
             | otherwise
                  = throwError "Value out of range"
      foobar
lEncNonExtConsInt realRC effRC v = throwError "Cannot encode MAX or MIN."
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
addUncLen encFun [] = lastLen k16 0
addUncLen encFun (x:xs)
    | l == 4 && last16 == k16 = blockLen 4 63 ++ (concat . map encFun) x
                                              ++ addUncLen encFun xs
    | l == 1 && last16 < k16  = lastLen k16 ((genericLength . head) x) ++ encFun (head x)
    | otherwise               = if last16 == k16
                                    then blockLen l 63 ++ (concat . map encFun) x ++ lastLen k16 0
                                    else blockLen (l-1) 63 ++ (concat . map encFun) (init x)
                                                           ++ lastLen k16 ((genericLength.last) x)
                                                           ++ encFun (last x)
    where
        l      = genericLength x
        last16 = (genericLength . last) x

k16 :: Integer
k16    = 16*(2^10)


lastLen :: Integer -> Integer -> [Int]
lastLen r n
   | n <= 127       = 0:(encodeNNBIntBits (n, 127))
   | n < r          = 1:0:(encodeNNBIntBits (n, (r-1)))
   | otherwise      = error "Length is out of range."

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

lEncodeEnum :: Enumerate a -> ExactlyOne a SelectionMade -> PerEncoding
lEncodeEnum e x
    = let (b,inds) = assignIndex e
          no = genericLength inds
      in
        encodeEnumAux b no inds e x

encodeEnumAux :: Bool -> Integer -> [Integer] -> Enumerate a -> ExactlyOne a n
                 -> PerEncoding
encodeEnumAux b no (f:r) (AddEnumeration  _ es) (AddAValue a rest)
    = if not b
        then return (encodeNNBIntBits (f, no-1))
        else return (0: encodeNNBIntBits (f, no-1))
encodeEnumAux b no (f:r) (AddEnumeration  _ es) (AddNoValue a rest)
    = encodeEnumAux b no r es rest
encodeEnumAux b no inds (EnumerationExtensionMarker   ex) x
    = let el = noEnums ex
      in encodeEnumExtAux 0 el ex x
encodeEnumAux _ _ _ _ _ = throwError "No enumerated value!"

encodeEnumExtAux :: Integer -> Integer -> Enumerate a -> ExactlyOne a n
                    -> PerEncoding
encodeEnumExtAux i l (AddEnumeration  _ es) (AddAValue a rest)
    = return (1:encodeNSNNInt i 0)
encodeEnumExtAux i l (AddEnumeration  _ es) (AddNoValue a rest)
    = encodeEnumExtAux (i+1) l es rest
encodeEnumExtAux i l _ _ = throwError "No enumerated extension value!"

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

\section{ENCODING THE BITSTRING TYPE}

\begin{code}

lEncodeBS :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PerEncoding
lEncodeBS nbs [] x = encodeBSNoSz nbs x
lEncodeBS nbs cl x = encodeBSSz nbs cl x


encodeBSSz :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PerEncoding
encodeBSSz nbs cl xs = lEncValidBS nbs (effBSCon cl) (validBSCon cl) xs

effBSCon ::[SubtypeConstraint BitString] -> Either String (ExtBS (ConType IntegerConstraint))
effBSCon cs = lSerialEffCons lBSConE top cs


validBSCon :: [SubtypeConstraint BitString] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validBSCon cs = lSerialEffCons lBSConE top cs


lEncValidBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> BitString -> PerEncoding
lEncValidBS nbs m n v
    = do
        vsc <- m
        if extensibleBS vsc
            then lEncExtBS nbs m n v
            else lEncNonExtBS nbs m n v


lEncNonExtBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> BitString
                -> PerEncoding
lEncNonExtBS nbs m n (BitString vs)
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
            Valid okrc = conType . getBSRC $ ok
            emptyConstraint = rc == bottom
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength vs
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | null nbs && inSizeRange okrc || (not . null) nbs
                    = do bs <- bsCode nbs rc vs
                         return bs
                | otherwise
                    = throwError "Value out of range"
        foobar


lEncExtBS :: NamedBits -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> BitString
                -> PerEncoding
lEncExtBS nbs m n (BitString vs)
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
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
                    = throwError "Empty constraint"
                | inSizeRange okrc
                    = do
                        bs <- bsCode nbs rc vs
                        return (0:bs)
                | inSizeRange okec
                    = do
                        bs <- bsExtCode nbs rc ec vs
                        return (1:bs)
                | otherwise
                    = throwError "Value out of range"
        foobar


--bsCode :: NamedBits ->
bsCode nbs rc xs
      =  let l  = lower rc
             u  = upper rc
             exs = if (not.null) nbs then editBS l u xs
                     else return xs
         in
             if u == 0
             then return []
             else if u == l && u <= 65536
                       then exs
                       else if u <= 65536
                            then let Val ub = u
                                     Val lb = l
                                 in do
                                     ls <- exs
                                     ln <- return (genericLength ls)
                                     return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ ls)
                            else do
                                    ls <- exs
                                    return (encodeBitsWithLength ls)


bsExtCode nbs rc ec xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
          exs = if (not.null) nbs then editBS l u xs
                     else return xs
      in
          if u <= 65536
             then let Val ub = u
                      Val lb = l
                  in do
                        ls <- exs
                        ln <- return (genericLength ls)
                        return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ ls)
             else do
                     ls <- exs
                     return (encodeBitsWithLength ls)


editBS :: InfInteger -> InfInteger -> BitStream -> PerEncoding
editBS l u xs
    = let lxs = genericLength xs
      in if lxs < l
        then add0s (l-lxs) xs
        else
            if lxs > u
             then rem0s (lxs-u) xs
             else return xs

add0s :: InfInteger -> BitStream -> PerEncoding
add0s (Val n) xs = return (xs ++ take (fromInteger n) [0,0..])
add0s _ _        = throwError "Invalid number input -- MIN or MAX."

rem0s :: InfInteger -> BitStream -> PerEncoding
rem0s (Val (n+1)) xs
    = if last xs == 0
           then rem0s (Val n) (init xs)
           else throwError "Last value is not 0"
rem0s (Val 0) xs = return xs
rem0s _ _  = throwError "Cannot remove a negative, MIN or MAX number of 0s."

\end{code}


\begin{code}
encodeBSNoSz :: NamedBits -> BitString -> PerEncoding
encodeBSNoSz nbs (BitString [])
    = return ([])
encodeBSNoSz nbs (BitString bs)
    = let rbs = reverse bs
          rem0 = if (not.null) nbs then strip0s rbs
            else rbs
          ln = genericLength rem0
       in
        return (encodeBitsWithLength (reverse rem0))



strip0s (a:r)
    = if a == 0
        then strip0s r
        else (a:r)
strip0s [] = []

\end{code}

\section{ENCODING THE OCTETSTRING TYPE}

\begin{code}

lEncodeOS :: [SubtypeConstraint OctetString] -> OctetString -> PerEncoding
lEncodeOS [] x = encodeOSNoSz x
lEncodeOS cl x = encodeOSSz cl x

\end{code}

encodeOctS encodes an unconstrained SEQUENCEOF value.

\begin{code}

encodeOSNoSz :: OctetString -> PerEncoding
encodeOSNoSz (OctetString xs)
    = let foo x = encodeNNBIntBits ((fromIntegral x),255)
      in
        return (encodeWithLength (concat . map foo) xs)


encodeOSSz :: [SubtypeConstraint OctetString] -> OctetString -> PerEncoding
encodeOSSz cl xs = lEncValidOS (effOSCon cl) (validOSCon cl) xs

effOSCon ::[SubtypeConstraint OctetString] -> Either String (ExtBS (ConType IntegerConstraint))
effOSCon cs = lSerialEffCons lOSConE top cs


validOSCon :: [SubtypeConstraint OctetString] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validOSCon cs = lSerialEffCons lOSConE top cs


lEncValidOS :: Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> OctetString -> PerEncoding
lEncValidOS m n v
    = do
        vsc <- m
        if extensibleBS vsc
            then lEncExtOS m n v
            else lEncNonExtOS m n v


lEncNonExtOS :: Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> OctetString
                -> PerEncoding
lEncNonExtOS m n (OctetString vs)
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
            Valid okrc = conType . getBSRC $ ok
            emptyConstraint = rc == bottom
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength vs
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | inSizeRange okrc
                    = do bs <- osCode rc vs
                         return bs
                | otherwise
                    = throwError "Value out of range"
        foobar


lEncExtOS :: Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> OctetString
                -> PerEncoding
lEncExtOS m n (OctetString vs)
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
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
                    = throwError "Empty constraint"
                | inSizeRange okrc
                    = do
                        bs <- osCode rc vs
                        return (0:bs)
                | inSizeRange okec
                    = do
                        bs <- osExtCode rc ec vs
                        return (1:bs)
                | otherwise
                    = throwError "Value out of range"
        foobar

osCode :: IntegerConstraint -> [Octet] -> PerEncoding
osCode rc xs
      =  let l  = lower rc
             u  = upper rc
             octetToBits x = encodeNNBIntBits ((fromIntegral x),255)
             octetsToBits  = (concat . map octetToBits)
         in
             if u == 0
             then return []
             else if u == l && u <= 65536
                       then return (octetsToBits xs)
                       else if u <= 65536
                            then let Val ub = u
                                     Val lb = l
                                 in do
                                     ln <- return (genericLength xs)
                                     return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ octetsToBits xs)
                            else return (encodeWithLength octetsToBits xs)

osExtCode :: IntegerConstraint -> IntegerConstraint -> [Octet] -> PerEncoding
osExtCode rc ec xs
    = let nc = rc `ljoin` ec
          l  = lower nc
          u  = upper nc
          octetToBits x = encodeNNBIntBits ((fromIntegral x),255)
          octetsToBits  = (concat . map octetToBits)
      in if u <= 65536
         then let Val ub = u
                  Val lb = l
              in do
                   ln <- return (genericLength xs)
                   return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ octetsToBits xs)
         else return (encodeWithLength octetsToBits xs)

\end{code}

\section{ENCODING THE SEQUENCE TYPE}

\begin{code}

lEncodeSeq :: Sequence a -> a -> PerEncoding
lEncodeSeq s x
    =   do ((rp,rb),(ap,ab)) <- encodeSeqAux ([],[]) ([],[]) s x
           if null ap
              then
                 return (concat rp ++ concat rb ++ concat ap ++ concat ab)
              else
                 return (concat rp ++ concat rb ++ lengthAdds ap ++ concat ab)

\end{code}

I DON'T THINK THAT THE ELSE CASE IS FRAGMENTING CORRECTLY

18.8 A length determinant of the number of extension additions is added if
the sequence has any extension additions declared. This is encoded as a normally
small length (10.9.3.4)

\begin{code}

lengthAdds ap
    = let la = genericLength ap
       in if la <= 63
        then 0:encodeNNBIntBits (la-1, 63) ++ concat ap
        else 1:encodeOctetsWithLength (encodeNNBIntOctets la) ++ concat ap

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
        bts <- lEncode a [] x
        encodeSeqAux (ap,ab) ([]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        bts <- lEncode a [] x
        encodeSeqAux (ap,ab) ([]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        bts <- lEncode a [] x
        encodeSeqAux (ap,ab) ([1]:rp,bts:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeSeqAux (ap,ab) ([0]:rp,[]:rb) as xs
encodeSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        bts <- lEncode a [] x
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
    = do bts <- lEncode a [] x
         encodeCO ([]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeCO ([]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do bts <- lEncode a [] x
         encodeCO ([]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        bts <- lEncode a [] x
        encodeCO ([1]:rp,bts:rb) as xs
encodeCO (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeCO ([0]:rp,[]:rb) as xs
encodeCO (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        bts <- lEncode a [] x
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
open type (using lEncodeOpen). If an addition is not present then a
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
    = do bts <- lEncodeOpen (BuiltinType (SEQUENCE a)) x
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do bts <- lEncodeOpen a x
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do bts <- lEncodeOpen a x
         encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs) =
   encodeExtSeqAux ([0]:ap,[]:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
   = do bts <- lEncodeOpen a x
        encodeExtSeqAux ([1]:ap,bts:ab) (rp,rb) as xs
encodeExtSeqAux (ap,ab) (rp,rb) _ _
    = throwError "Impossible case for extension addition."


\end{code}

\section{ENCODING THE SEQUENCE-OF TYPE}

encodeSO implements the encoding of an unconstrained
sequence-of value. This requires both the encoding of
each of the components, and in most cases the encoding
of the length of the sequence-of (which may require
fragmentation into 64K blocks).

\begin{code}

lEncodeSeqOf :: [SubtypeConstraint [a]] -> ASNType a -> [a] -> PerEncoding
lEncodeSeqOf [] t x = lEncodeUncSeqOf t x
lEncodeSeqOf cl t x = lEncodeConSeqOf t cl x


\end{code}

lEncodeUncSeqOf encodes an unconstrained SEQUENCEOF value.

\begin{code}

lEncodeUncSeqOf :: ASNType a -> [a] -> PerEncoding
lEncodeUncSeqOf t xs = mEncodeWithLength (encodeList t) xs


--mEncodeWithLength :: ([t] -> PerEncoding) -> [t] -> PerEncoding
mEncodeWithLength fun xs
    = do
           ls <- return ((groupBy 4 . groupBy (16*(2^10))) xs)
           mAddUncLen fun ls


--mAddUncLen :: ([b] -> PerEncoding) -> [[[b]]] -> PerEncoding
mAddUncLen encFun [] = return (lastLen k16 0)
mAddUncLen encFun (x:xs)
    | l == 4 && last16 == k16
        = do
            bl <- return (blockLen 4 63)
            bs <- encFun x
            ls <- mAddUncLen encFun xs
            return (bl ++ bs ++ ls)
    | l == 1 && last16 < k16
        = do
            ll <- return (lastLen k16 ((genericLength . head) x))
            bs <- encFun ([head x])
            return (ll ++ bs)
    | last16 == k16
        = do
            bl <- return (blockLen l 63)
            bs <- encFun x
            ll <- return (lastLen k16 0)
            return (bl ++ bs ++ ll)
    | otherwise
        = do
            bl <- return (blockLen (l-1) 63)
            bs <- encFun (init x)
            ll <- return (lastLen k16 ((genericLength.last) x))
            ls <- encFun ([last x])
            return (bl ++ bs ++ ll ++ ls)
    where
        l      = genericLength x
        last16 = (genericLength . last) x

\end{code}


\begin{code}

lEncodeConSeqOf :: ASNType a -> [SubtypeConstraint [a]] -> [a] -> PerEncoding
lEncodeConSeqOf t cl xs = lEncValidSeqOf t (effSeqOfCon cl) (validSeqOfCon cl) xs

effSeqOfCon ::[SubtypeConstraint [a]] -> Either String (ExtBS (ConType IntegerConstraint))
effSeqOfCon cs = lSerialEffCons lSeqOfConE top cs


validSeqOfCon :: [SubtypeConstraint [a]] -> Either String (ExtBS (ConType ValidIntegerConstraint))
validSeqOfCon cs = lSerialEffCons lSeqOfConE top cs


lEncValidSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
               -> Either String (ExtBS (ConType ValidIntegerConstraint))
               -> [a] -> PerEncoding
lEncValidSeqOf t m n v
    = do
        vsc <- m
        if extensibleBS vsc
            then lEncExtSeqOf t m n v
            else lEncNonExtSeqOf t m n v

lEncNonExtSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> [a]
                -> PerEncoding
lEncNonExtSeqOf t m n vs
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
            Valid okrc = conType . getBSRC $ ok
            emptyConstraint = rc == bottom
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength vs
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | inSizeRange okrc
                    = do bs <- soCode rc t vs
                         return bs
                | otherwise
                    = throwError "Value out of range"
        foobar


soCode rc t xs
      =  let l  = lower rc
             u  = upper rc
         in
             if u == 0
             then return []
             else if u == l && u <= 65536
                       then encodeAll t xs
                       else if u <= 65536
                            then let Val ub = u
                                     Val lb = l
                                 in do
                                     ln <- return (genericLength xs)
                                     bs <- encodeAll t xs
                                     return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ bs)
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
                                     ln <- return (genericLength xs)
                                     bs <- encodeAll t xs
                                     return (encodeNNBIntBits ((ln-lb), (ub-lb)) ++ bs)
                            else do
                                    mEncodeWithLength (encodeList t) xs


encodeList t [] = return []
encodeList t (f:r)
    = do
        bs <- encodeAll t f
        rs <- encodeList t r
        return (bs ++ rs)


encodeAll t (f:r)
    = do
        x <- lEncode t [] f
        r <- encodeAll t r
        return (x ++ r)
encodeAll t [] = return []


lEncExtSeqOf :: ASNType a -> Either String (ExtBS (ConType IntegerConstraint))
                -> Either String (ExtBS (ConType ValidIntegerConstraint))
                -> [a]
                -> PerEncoding
lEncExtSeqOf t m n vs
    = do
        vsc <- m
        ok  <- n
        let rc = conType . getBSRC $ vsc
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
                    = throwError "Empty constraint"
                | inSizeRange okrc
                    = do
                        bs <- soCode rc t vs
                        return (0:bs)
                | inSizeRange okec
                    = do
                        bs <- soExtCode rc ec t vs
                        return (1:bs)
                | otherwise
                    = throwError "Value out of range"
        foobar

\end{code}


\section{ENCODING THE SET TYPE}

Encoding the SET type. The encoding is the same as for a
SEQUENCE except that the components must be canonically ordered.
The ordering is based on the component's tags. Note, the
preamble must be reordered to match the ordering of the
components.

\begin{code}

lEncodeSet :: Sequence a -> a -> PerEncoding
lEncodeSet s x
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

lEncodeChoice :: Choice a -> ExactlyOne a SelectionMade -> PerEncoding
lEncodeChoice c x
    =   do ts  <- return (getCTags c)
           (ea, ec) <- (encodeChoiceAux [] [] c x)
           if length ec == 1
               then return (concat ec)
               else
                let ps  = zip ts ec
                    os  = mergesort choicePred ps
                    pps = zip [0..] os
                    fr  = (head . filter (not . nullValue)) pps
                    ls  = genericLength os
                in
                 if null ea
                 then return (encodeNNBIntBits (fst fr,ls-1) ++ (snd .snd) fr)
                    else
                    if length ec <= 63
                    then return (ea ++ 0:encodeNNBIntBits (fst fr, 63) ++ (snd.snd) fr)
                    else return (ea ++ 1:encodeOctetsWithLength (encodeNNBIntOctets (fst fr)) ++ (snd.snd) fr)

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
        bts <- lEncode a [] x
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
    = do bts <- lEncodeOpen a x
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

lEncodeRCS :: (Eq a, RS a, Lattice a)
              => SerialSubtypeConstraints a -> a -> PerEncoding
lEncodeRCS [] vs
        | rcsMatch vs top
            = return (encodeResString vs)
        | otherwise
            = throwError "Invalid value!"
lEncodeRCS cs vs
        | rcsMatch vs top
            = lEncValidRCS (effCon cs) (validCon cs) vs
        | otherwise
            = throwError "Invalid value!"


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
                 -> a -> PerEncoding
lEncValidRCS m n v
    = do
        vsc <- m
        if extensible vsc
            then lEncExtRCS m n v
            else lEncNonExtRCS m n v


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
                -> PerEncoding
lEncNonExtRCS m n vs
    = do
        vsc <- m
        ok  <- n
        let rc = getRC vsc
            okrc = getRC ok
            sc = getSC rc
            Valid oksc = getSC okrc
            pac = getPAC rc
            emptyConstraint = rc == bottom
            noSC  = sc == top
            noPAC = pac == top
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength v
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            v = getString vs
            inPA x  = stringMatch v (getString x)
            foobar
                | emptyConstraint
                    = throwError "Empty constraint"
                | not noSC && not noPAC && inPA pac && inSizeRange oksc
                    = return (lEncodeRCSSzF sc pac vs)
                | noSC && not noPAC && inPA pac
                    = return (lEncodeRCSF pac vs)
                | noPAC && not noSC && inSizeRange oksc
                    = return (lEncodeRCSSz sc vs)
                | otherwise
                    = throwError "Value out of range"
        foobar


lEncExtRCS :: (RS a, Eq a, Lattice a) =>
              Either String (ExtResStringConstraint (ResStringConstraint a IntegerConstraint))
              -> Either String (ExtResStringConstraint (ResStringConstraint a ValidIntegerConstraint))
              -> a
              -> PerEncoding
lEncExtRCS m n vs
    = do
        vsc <- m
        ok <- n
        let rc = getRC vsc
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
            emptyConstraint = vsc == bottom
            noRC  = rc == top
            noEC  = ec == top
            noRSC  = rsc == top
            noRPAC = rpac == top
            noESC  = esc == top
            noEPAC = epac == top
            inSizeRange []      = False
            inSizeRange (x:rs)
                = let l = genericLength (getString vs)
                  in l >= (lower x) && l <= (upper x) || inSizeRange rs
            inPA x  = stringMatch (getString vs) (getString x)
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
                    = return (0:lEncodeRCSF rpac vs)
                | noRPAC && inSizeRange okrsc
                    = return (0:lEncodeRCSSz rsc vs)
                | inPA rpac && inSizeRange okrsc
                    = return (0:lEncodeRCSSzF rsc rpac vs)
                | otherwise
                    = throwError "Value out of range"
            foobarEC
                | noESC && inPA epac
                    = return (1:lEncodeRCSF top vs)
                | noEPAC && inSizeRange okesc
                    = return (1:encodeResString vs)
                | inPA epac && inSizeRange okesc
                    = return (1:lEncodeRCSF top vs)
                | otherwise
                    = throwError "Value out of range"
            foobarBoth
                | not noRPAC && inPA rpac && not noRSC && inSizeRange okrsc
                    = return (0:lEncodeRCSSzF rsc rpac vs)
                | noRPAC && noEPAC && not noRSC && inSizeRange okrsc
                    = return (0:lEncodeRCSSz rsc vs)
                | noRSC && noESC && not noRPAC && inPA rpac
                    = return (0:lEncodeRCSF rpac vs)
                | noRPAC && noEPAC && not noESC && inSizeRange okesc
                     = return (1:encodeResString vs)
                | (not noRSC && inSizeRange okrsc && noRPAC && not noEPAC && inPA epac) ||
                  (not noRSC && inSizeRange okrsc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (not noESC && inSizeRange okesc && not noRPAC && inPA rpac) ||
                  (not noESC && inSizeRange okesc && noRPAC && not noEPAC && inPA epac) ||
                  (not noESC && inSizeRange okesc && not noRPAC && not noEPAC && not (inPA epac) && inPA expac) ||
                  (noRSC && noESC && ((noRPAC && not noEPAC && inPA epac) ||
                  (not noRPAC && not noEPAC && not (inPA epac) && inPA expac)))
                     =  return (1:lEncodeRCSF top vs)
                | otherwise
                     = throwError "Value out of range"
        foobar

lEncodeRCSSz :: (RS a, Lattice a) => IntegerConstraint -> a -> BitStream
lEncodeRCSSz (IntegerConstraint l u) v
    = let t = getTop v
          gl = genericLength (getString t)
       in
        manageRCS (encSF (getString t)) makeString encodeResString getString l u v


manageRCS :: (RS a, Lattice a) => (String -> BitStream) -> (String -> a) ->
                       (a -> BitStream) -> (a -> String) -> InfInteger
                        -> InfInteger -> a -> BitStream
manageRCS e f g h l u v
    = manageExtremes e (g . f) l u (h v)


encodeResString :: (RS a, Lattice a) => a -> BitStream
encodeResString vs
    = let t = getTop vs
          l = genericLength (getString t)
      in
         encodeWithLength (encSF (getString t))  (getString vs)

getTop :: (RS a, Lattice a) => a -> a
getTop m = top

encC :: Integer -> Char -> BitStream
encC i c = encodeNNBIntBits ((fromIntegral.ord) c, i)

encS :: Integer -> String -> BitStream
encS i s  = (concat . map (encC i)) s

\end{code}

 27.5.4 Encoding of a RESTRICTED CHARACTER STRING with a permitted alphabet
 constraint.

\begin{code}

lEncodeRCSSzF :: (RS a) => IntegerConstraint -> a -> a -> BitStream
lEncodeRCSSzF (IntegerConstraint l u) rcs1 rcs2
        =  manageExtremes (encSF (getString rcs1))
                          (lEncodeRCSF rcs1 . makeString) l u (getString rcs2)

lEncodeRCSF :: (RS a) => a -> a -> BitStream
lEncodeRCSF rcs1 rcs2 = encodeWithLength (encSF (getString rcs1)) (getString rcs2)


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
                concat (canEnc (lp-1) sp str)


minExp n e p
    = if n^e < p
        then minExp n (e+1) p
        else e

-- The first two cases are described in X.691 27.5.6 and 25.5.7
-- and the last case by 10.9 Note 3.

manageExtremes :: ([a] -> BitStream) -> ([a] -> BitStream) -> InfInteger
                        -> InfInteger -> [a] -> BitStream
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
                        in encodeNNBIntBits ((genericLength x - v), r-1) ++ fn1 x

\end{code}

Clause 38.8 in X680 encoding based on canonical ordering of restricted character string characters

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

type ElementSetSpecs a = SubtypeConstraint a

fromPER x = decode4 x []

decode4 (BuiltinType t) cl = fromPer3 t cl
decode4 (ConstrainedType t c) cl = decode4 t (c:cl)
decode4 (ReferencedType r t) cl  = decode4 t cl

fromPer3 :: (MonadError ASNError (t BG.BitGet), MonadTrans t) =>
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
   (MonadError ASNError (t BG.BitGet), MonadTrans t) =>
   IntegerConstraint -> (Integer -> ASNType a -> t BG.BitGet [b]) -> ASNType a -> t BG.BitGet [b]
decodeLengthDeterminant c f t
   | ub /= maxBound &&
     ub == lb &&
     v <= 64*(2^10) = f v t
   | ub == maxBound = decodeLargeLengthDeterminant3' f t
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

data ASNError =
     ConstraintError String
   | BoundsError     String
   | DecodeError     String
   | ExtensionError  String
   | OtherError      String
      deriving Show

instance Error ASNError where
   noMsg = OtherError "The impossible happened"

errorize (Left e)  = throwError (ConstraintError e)
errorize (Right x) = return x

decodeInt3 :: (MonadError ASNError (t BG.BitGet), MonadTrans t) => [ElementSetSpecs InfInteger] -> t BG.BitGet InfInteger
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

lDecConsInt3 :: (MonadError ASNError (t BG.BitGet), MonadTrans t) =>
                 t BG.BitGet IntegerConstraint -> Bool -> t BG.BitGet IntegerConstraint -> t BG.BitGet InfInteger
lDecConsInt3 mrc isExtensible mec =
   do rc <- mrc
      ec <- mec
      let extensionConstraint    = ec /= bottom
          tc                     = rc `ljoin` ec
          extensionRange         = fromIntegral $ let (Val x) = (upper tc) - (lower tc) + (Val 1) in x -- fromIntegral means there's an Int bug lurking here
          rootConstraint         = rc /= bottom
          rootLower              = let Val x = lower rc in x
          rootRange              = fromIntegral $ let (Val x) = (upper rc) - (lower rc) + (Val 1) in x -- fromIntegral means there's an Int bug lurking here
          numOfRootBits          = genericLength (encodeNNBIntBits (rootRange - 1, rootRange - 1))
          numOfExtensionBits     = genericLength (encodeNNBIntBits (extensionRange - 1, extensionRange - 1))
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

decodeUInt3 :: (MonadError ASNError (t BG.BitGet), MonadTrans t) => t BG.BitGet Integer
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

decodeSEQUENCEAux :: (MonadError ASNError (t BG.BitGet), MonadTrans t) => BitMap -> Sequence a -> t BG.BitGet a
decodeSEQUENCEAux _ EmptySequence = return Empty -- ignoring the bit map doesn't look right - it's probably an error if it's not empty
decodeSEQUENCEAux bitmap (AddComponent (MandatoryComponent (NamedType _ t)) ts) =
   do x <- decode4 t []
      xs <- decodeSEQUENCEAux bitmap ts
      return (x :*: xs)

\end{code}

\begin{code}

forget :: (MonadTrans t, MonadError [Char] (t BG.BitGet)) => Either String (t BG.BitGet a) -> t BG.BitGet a
forget (Left e) = throwError e
forget (Right x) = x

swap :: (Functor m, Monad m) => Either String (m a) -> m (Either String a)
swap (Left s) = return (Left s)
swap (Right x) = fmap Right x

\end{code}

\section{SEQUENCE OF Decoding}

\begin{code}

nSequenceOfElements n e = sequence . genericTake n . repeat . flip decode4 e

decodeSequenceOf :: (MonadError ASNError (t BG.BitGet), MonadTrans t) =>
                    ASNType a -> [ElementSetSpecs [a]] -> t BG.BitGet [a]
decodeSequenceOf t [] = decodeLargeLengthDeterminant3' (flip nSequenceOfElements []) t
decodeSequenceOf t cs = decodeSequenceOfAux t (errorize (effSeqOfCon cs)) (errorize (validSeqOfCon cs))

decodeSequenceOfAux :: (MonadError ASNError (t BG.BitGet), MonadTrans t) =>
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

decodeBitString :: (MonadError ASNError (t BG.BitGet), MonadTrans t) => [ElementSetSpecs BitString] -> t BG.BitGet BitString
decodeBitString constraints =
   do xs <- decodeBitStringAux (errorize (lSerialEffCons lBSConE top constraints))
      return (BitString . concat . (map bitString) $ xs)

decodeBitStringAux :: (MonadError ASNError (t BG.BitGet), MonadTrans t) => t BG.BitGet (ExtBS (ConType IntegerConstraint)) -> t BG.BitGet [BitString]
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

\section{Bibliography}

\bibliographystyle{plainnat}

\bibliography{3gpp,ASN1}

\section{Appendix: Tests}

%include TestCTR.lhs

\end{document}
v v v v v v v

*************

^ ^ ^ ^ ^ ^ ^