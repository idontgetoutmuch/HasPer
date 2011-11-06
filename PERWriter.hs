{-# LANGUAGE MultiParamTypeClasses, GADTs, TypeOperators, EmptyDataDecls,
             FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving,
             ScopedTypeVariables, PatternGuards, DoRec, TypeSynonymInstances #-}

{-# OPTIONS_GHC -fwarn-unused-binds -fwarn-unused-imports #-}

{-  -fwarn-incomplete-patterns -fwarn-unused-matches  -}

-- Conventions
-- 
-- In order make the code more intelligible without using overlong identifiers, we adopt
-- the following conventions:
-- 
-- * All encoding functions begin with ``e''.
--
-- * All decoding functions begin with ``d''.
--
-- * A part of an identifier ``Cons'' is short form for ``Constrained''.
--
-- * A part of an identifier ``Uncons'' is short form for ``Unconstrained''.

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

type PERMonad = WriterT BB.BitBuilder (ErrorT ASNError Identity)

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

completeEncode :: PERMonad () -> PERMonad ()
completeEncode m
   =  {- X691REF: 10.1 -}
      let bs = extractValue m
      in case bs of
           {- X691REF: 10.1.3 with empty bit string -}
           (Right (f,s)) -> if BL.null $ BB.toLazyByteString s 
    	       	      	    	 then tell $ BB.fromBits 8 (0x00::Int)	 
			         else m
           {- X691REF: 10.1.3 with non-empty bit string -}
           x -> m

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
toPER (SEQUENCE s) x cl    = eSequence s x -- no PER-Visible constraints
toPER (SEQUENCEOF s) x cl  = eSequenceOf cl ((snd . splitName) s) x
toPER (SET s) x cl         = encodeSet s x -- no PER-Visible constraints
toPER (CHOICE c) x cl      = encodeChoice c x -- no PER-visible constraints
toPER (SETOF s) x cl       = encodeSetOf cl ((snd . splitName)s) x -- no PER-visible constraints
toPER (TAGGED tag t) x cl  = encode t cl x

fromPER :: ASNBuiltin a -> [ElementSetSpecs a] -> UnPERMonad a
fromPER t@INTEGER cl = dInteger cl
-- FIXME: Why are we ignoring the constraints?
fromPER t@(SEQUENCE s) cl = dSequence s

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

{- FIXME: I think this is as good as it's worth doing for now -}
{- Clearly we want to just say e.g. tell 1                    -}
{- Or do we. It is meant to return a bit-field value and not just a bit -}
{- So the following whould be fine. -}
encodeBool :: [SubtypeConstraint Bool] -> Bool -> PERMonad ()
encodeBool t x = tell $ BB.singleton x


------------------------------------------------------------------------
-- Integer types

-- FIXME: We normally stay in the monad and propogate any errors --- so make eitherExtensible redundant

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

encodeNonNegBinaryIntInOctets :: InfInteger -> PERMonad ()
encodeNonNegBinaryIntInOctets (Val x) = h 8 x where
   h p 0 = tell $ L.foldr BB.append BB.empty (L.replicate p (BB.singleton False))
   h 0 n = h 7       (n `div` 2) >> (tell . BB.fromBits 1) n
   h p n = h (p - 1) (n `div` 2) >> (tell . BB.fromBits 1) n
encodeNonNegBinaryIntInOctets y = throwError . OtherError $ "Cannot encode: " ++ show y

encodeOctetsWithLength :: BL.ByteString -> PERMonad ()
encodeOctetsWithLength bs
    = encodeUnconstrainedLength (tell . BB.fromBits 8) $ BL.unpack bs


encodeBitsWithLength :: BitStream -> PERMonad ()
encodeBitsWithLength = encodeUnconstrainedLength (tell . BB.fromBits 1)

minBits :: Integer -> Integer
minBits n = f n 0
   where
      f 0 a = a
      f n a = f (n `div` 2) (a+1)

-- FIXME: owner=Dan Why do we have SubtypeConstraint? Isn't the right terminology ElementSetSpecs?

type ElementSetSpecs a = SubtypeConstraint a

isEmptyConstraint, isNonEmptyConstraint :: (Eq t, Lattice t) => t -> Bool
isEmptyConstraint    x  = x == bottom
isNonEmptyConstraint x  = x /= bottom

inRangeSingle :: InfInteger -> IntegerConstraint -> Bool
inRangeSingle n c =  n >= (lower c) && n <= (upper c)

inRange :: InfInteger -> ValidIntegerConstraint -> Bool
inRange n vc | Valid cs <- vc = or . map (inRangeSingle n) $ cs

eInteger :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
eInteger [] v = eUnconsInteger v
eInteger cs v = eConsInteger cs v

eUnconsInteger :: InfInteger -> PERMonad ()
eUnconsInteger (Val x) = {- X691REF: 12.2.4 -}
                         encodeOctetsWithLength .
                         BP.runBitPut .
                         I.to2sComplementM  $ x
eUnconsInteger v       = throwError (BoundsError ("Cannot encode " ++ show v))

eConsInteger :: [SubtypeConstraint InfInteger] -> InfInteger -> PERMonad ()
eConsInteger cs v    = do
      actualCon    <- evaluateConstraint' pvIntegerElements top cs
      effectiveCon <- evaluateConstraint' pvIntegerElements top cs
      if isExtensible effectiveCon
        then {- X691REF: 12.1 -} eExtConsInteger    actualCon effectiveCon v
        else {- X691REF: 12.2 -} encodeNonExtConsInt actualCon effectiveCon v

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

eSemiConsInteger :: InfInteger -> InfInteger -> PERMonad ()
eSemiConsInteger x@(Val _) lb@(Val _) =  encodeNonNegBinaryIntInOctets $ x - lb
eSemiConsInteger x (Val _)
    = throwError . BoundsError $ "Cannot encode " ++ show x ++ "."
eSemiConsInteger _ _
    = throwError . ConstraintError $ "No lower bound."

dInteger :: [ElementSetSpecs InfInteger] -> UnPERMonad InfInteger
dInteger [] = dConsInteger top undefined top
dInteger cs = do
   effectiveCon <- evaluateConstraint' pvIntegerElements top cs
   let effRoot = getRootConstraint effectiveCon
       effExt  = getExtConstraint effectiveCon
   dConsInteger effRoot (isExtensible effectiveCon) effExt

dUnconInteger :: UnPERMonad Integer
dUnconInteger =
   liftM from2sComplement' $ decodeLargeLengthDeterminant chunkBy8 undefined
   where
      chunkBy8 :: Integer -> a -> UnPERMonad B.ByteString
      chunkBy8 n _ =
        lift $ (flip (const (BG.getLeftByteString . fromIntegral . (*8)))) n undefined

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

------------------------------------------------------------------------
-- Enumerated types

encodeEnum :: Enumerate -> SerialSubtypeConstraints Name -> Name -> PERMonad ()
encodeEnum e cs n
    =  let (extensible,inds) = assignIndex e {- X691REF: 13.1 -}
           no = L.genericLength inds
           (b,p) = validEnum e n 0
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

encodeNSNNInt :: Integer -> Integer -> PERMonad ()
encodeNSNNInt n lb
    = if n <= 63
        then do {- X691REF: 10.6.1 -}
                zeroBit
                toNonNegBinaryInteger (fromInteger n) (fromInteger 63)
        else do {- X691REF: 10.6.2 -}
                oneBit
                eSemiConsInteger (fromInteger n) (fromInteger lb)

------------------------------------------------------------------------
-- Bit string types

encodeBitstring :: NamedBits -> [SubtypeConstraint BitString] -> BitString -> PERMonad ()
encodeBitstring nbs [] x
    = {- X691REF: 15.2 -}
      encodeUnconstrainedBitstring nbs x
encodeBitstring nbs cs x
    = {- X691REF: 15.3 -}
      encodeBitstringWithConstraint nbs cs x

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

-- FIXME: Should we use higher order functions here rather than recursion?

rem0s :: InfInteger -> InfInteger -> BitStream -> BitStream
rem0s (Val 0) l xs = rem0s' l xs
rem0s (Val n) l xs = rem0s (Val (n - 1)) l (init xs)

rem0s' :: InfInteger -> BitStream -> BitStream
rem0s' l xs
    = if L.genericLength xs > l && last xs == 0
        then rem0s' l (init xs)
        else xs

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

------------------------------------------------------------------------
-- Octet string types

encodeOctetstring :: [SubtypeConstraint OctetString] -> OctetString -> PERMonad ()
encodeOctetstring [] x
    = {- X691REF: 16.8 with ub unset -}
      encodeUnconstrainedOctetstring x
encodeOctetstring cs x
    = {- X691REF: 16.3 -}
      encodeOctetstringWithConstraint cs x

encodeUnconstrainedOctetstring :: OctetString -> PERMonad ()
encodeUnconstrainedOctetstring (OctetString xs)
    = encodeUnconstrainedLength encodeOctet xs

encodeOctet :: Octet -> PERMonad ()
encodeOctet x = toNonNegBinaryInteger (fromIntegral x) 255

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

-- FIXME: We should make these newtypes
type OptDefBits = BitStream
type ExtBits = BitStream

-- FIXME: This should really be empty in a separate module and then we can import it as
-- FIXME: e.g. BS.empty
emptyBitStream :: BitStream
emptyBitStream = []

-- FIXME: Ditto
emptySubTypeConstraints :: SerialSubtypeConstraints a
emptySubTypeConstraints = []

data Ext  = Ext  | NotExt  deriving Eq
data Used = Used | NotUsed deriving Eq
type ExtAndUsed = (Ext, Used)

eSequence :: Sequence a -> a -> PERMonad ()
eSequence s v
           = do _odbs <- pass $ eSequenceAux NotExt NotUsed emptyBitStream s v
                return ()

-- FIXME: Eugh pattern match failure here
selectOutput (Right (a,b)) = b
selectOutput (Left s)      = error $ show s

eSequenceAux :: Ext ->
                Used ->
                OptDefBits ->
                Sequence a ->
                a ->
                PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)
eSequenceAux ext used optDef EmptySequence Empty
    = return (optDef, completeSequenceBits (ext, used) optDef)
eSequenceAux NotExt _ optDefBits (ExtensionMarker as) xs
   = do rec (b, eb, _, pm)       <- censor (BB.append extRoot . BB.append extAddPreamble) $
                                    eSequenceAuxExt (Ext, NotUsed) optDefBits emptyBitStream as xs
            {- X691REF: 18.8 -}
            ((), extAddPreamble) <- censor (const BB.empty) $ listen $ addExtensionAdditionPreamble eb
            {- X691REF: 18.2 -}
            ((od2, _), extRoot)  <- pass ((,) <$> (listen pm) <*> (pure $ const BB.empty))
        eSequenceAux (fst b) (snd b) od2 EmptySequence Empty

eSequenceAux Ext used optDefBits (ExtensionMarker as) xs
   = eSequenceAux Ext used optDefBits as xs

eSequenceAux e u od (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do od2 <- eSequenceAuxCO [] s x
         -- FIXME: A list looks like the wrong type for putting things at the end
         eSequenceAux e u (od ++ od2) as xs

eSequenceAux e u od (AddComponent (ComponentsOf (ReferencedType n t)) as) (x:*:xs)
    = eSequenceAux e u od (AddComponent (ComponentsOf t) as) (x:*:xs)

eSequenceAux e u od (AddComponent (ComponentsOf (ConstrainedType t c)) as) (x:*:xs)
    = eSequenceAux e u od (AddComponent (ComponentsOf t) as) (x:*:xs)

eSequenceAux e u od (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do encode a emptySubTypeConstraints x
         eSequenceAux e u od as xs

eSequenceAux e u od (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    = eSequenceAux e u od as xs

eSequenceAux b1 b2 od (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = eSequenceAux b1 Used od as xs

eSequenceAux e u od (AddComponent (OptionalComponent (NamedType _ a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with optional component not present -}
        eSequenceAux e u (od ++ [0]) as xs

eSequenceAux e u od (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.2 with optional component present -}
         encode a emptySubTypeConstraints x
         eSequenceAux e u (od ++ [1]) as xs

eSequenceAux e u od (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    =   {- X691REF: 18.2 with default value -}
        {- X691REF: 18.5 with default value (CANONICAL-PER) -}
        eSequenceAux e u (od ++ [0]) as xs

eSequenceAux e u od (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do {- X691REF: 18.2 with non-default value -}
         encode a emptySubTypeConstraints x
         eSequenceAux e u (od ++ [1]) as xs

eSequenceAux extension _ optDef (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = eSequenceAux extension Used optDef as xs

completeSequenceBits :: ExtAndUsed -> BitStream -> BB.BitBuilder -> BB.BitBuilder
completeSequenceBits (extensible, extensionAdditionPresent) odb bs
    | extensible == NotExt
        = BB.append (fragment odb) bs
    | extensionAdditionPresent == Used
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

eSequenceAuxExt :: ExtAndUsed ->
                   OptDefBits ->
                   ExtBits ->
                   Sequence a ->
                   a ->
                   PERMonad ((ExtAndUsed, ExtBits, OptDefBits, PERMonad (OptDefBits, BB.BitBuilder -> BB.BitBuilder)))
eSequenceAuxExt b odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        eSequenceAuxExt b odb (eb ++ [0]) as xs
eSequenceAuxExt (b1,b2) odb eb (AddComponent (ExtensionComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ComponentType extension -}
         encodeOpen a x
         eSequenceAuxExt (b1,Used) odb (eb ++ [1]) as xs
eSequenceAuxExt b odb eb (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        eSequenceAuxExt b odb (eb ++ [0]) as xs
eSequenceAuxExt (b1,b2) odb eb (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ComponentType extension -}
         encodeOpen a x
         eSequenceAuxExt (b1,Used) odb (eb ++ [1]) as xs
eSequenceAuxExt b odb eb (ExtensionAdditionGroup _ a as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        eSequenceAuxExt b odb (eb ++ [0]) as xs
eSequenceAuxExt (b1,b2) odb eb (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ExtensionAdditionGroup extension -}
         encodeOpen (BuiltinType (SEQUENCE (makeSequence a))) x
         eSequenceAuxExt (b1, Used) odb (eb ++ [1]) as xs
eSequenceAuxExt b odb eb (ExtensionMarker as) xs
    = return (b, eb, odb, eSequenceAux (fst b) (snd b) odb as xs)
eSequenceAuxExt b odb eb EmptySequence Empty
    = return (b, eb, odb, eSequenceAux (fst b) (snd b) odb EmptySequence Empty)
eSequenceAuxExt b odb eb _ _
    = throwError (OtherError "Inappropriate component!")

addExtensionAdditionPreamble :: OptDefBits -> PERMonad ()
addExtensionAdditionPreamble []
    = do noBit
addExtensionAdditionPreamble ap
    = let la = genericLength ap
       in if la <= 64
        then do {- X691REF: 10.9.3.4  when n <= 64-}
                zeroBit
                toNonNegBinaryInteger (la - 1) 63
                tell (toBitBuilder ap)
        else do {- X691REF: 10.9.3.4  when n > 64-}
                oneBit
                encodeNonNegBinaryIntInOctets la
                tell (toBitBuilder ap)

eSequenceAuxCO :: OptDefBits -> Sequence a -> a -> PERMonad OptDefBits
eSequenceAuxCO odb EmptySequence _
    = return odb
eSequenceAuxCO odb (ExtensionMarker as) xs
    = eSequenceAuxCO odb as xs
eSequenceAuxCO odb (AddComponent (ComponentsOf (BuiltinType (SEQUENCE s))) as) (x:*:xs)
    = do odb2 <- eSequenceAuxCO [] s x
         eSequenceAuxCO (odb ++ odb2) as xs
eSequenceAuxCO odb (AddComponent (ComponentsOf _) as) (x:*:xs)
    = throwError (OtherError "COMPONENTS OF can only be applied to a SEQUENCE")
eSequenceAuxCO odb (AddComponent (MandatoryComponent (NamedType t a)) as) (x:*:xs)
    = do encode a [] x
         eSequenceAuxCO odb as xs
eSequenceAuxCO odb (AddComponent (ExtensionComponent (NamedType t a)) as) (_:*:xs) =
   eSequenceAuxCO odb as xs
eSequenceAuxCO odb (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs) =
   eSequenceAuxCO (odb ++ [0]) as xs
eSequenceAuxCO odb (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do
        encode a [] x
        eSequenceAuxCO (odb ++ [1]) as xs
eSequenceAuxCO odb (AddComponent (DefaultComponent (NamedType t a) d) as) (Nothing:*:xs)
    = eSequenceAuxCO (odb ++ [0]) as xs
eSequenceAuxCO odb (AddComponent (DefaultComponent (NamedType t a) d) as) (Just x:*:xs)
    = do
        encode a [] x
        eSequenceAuxCO (odb ++ [1]) as xs
eSequenceAuxCO odb (ExtensionAdditionGroup _ _ as) (x:*:xs)
    = eSequenceAuxCO odb as xs

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

eSequenceOf :: [SubtypeConstraint [a]] -> ASNType a -> [a] -> PERMonad ()
eSequenceOf [] t x
    =   {- X691REF: 19.6 with ub unset -}
        encodeUnconstrainedSequenceOf t x
eSequenceOf cl t x
    =   eSequenceOfWithConstraint t cl x

encodeUnconstrainedSequenceOf :: ASNType a -> [a] -> PERMonad ()
encodeUnconstrainedSequenceOf t xs = encodeUnconstrainedLength (encode t []) xs

eSequenceOfWithConstraint :: ASNType a -> [SubtypeConstraint [a]] -> [a]
                                  -> PERMonad ()
eSequenceOfWithConstraint t cs v
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

encodeSet :: Sequence a -> a -> PERMonad ()
encodeSet s v 
           = do odb <- pass $ encodeSetAux (NotExt, NotUsed) [] s v
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
    | extensible == NotExt
        = let m = encodeSetAuxExt (Ext, NotUsed) ms [] as xs
          in
           do (b, eb,pm) <- censor (const BB.empty) m
              (od2,f) <- pm
              {- X691REF: 18.8 -}
              censor (BB.append (selectOutput . extractValue $ addExtensionAdditionPreamble eb)) m
              eSequenceAux (fst b) (snd b) od2 EmptySequence Empty 
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
    = encodeSetAux (b1, Used) ms as xs
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
    = encodeSetAux (b1,Used) ms as xs



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
         encodeSetAuxExt (b1,Used) ms (eb ++ [1]) as xs
encodeSetAuxExt b ms eb (AddComponent (OptionalComponent (NamedType t a)) as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSetAuxExt b ms (eb ++ [0]) as xs
encodeSetAuxExt (b1,b2) ms eb (AddComponent (OptionalComponent (NamedType t a)) as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ComponentType extension -}
         encodeOpen a x
         encodeSetAuxExt (b1,Used) ms (eb ++ [1]) as xs
encodeSetAuxExt b ms eb (ExtensionAdditionGroup _ a as) (Nothing:*:xs)
    =   {- X691REF: 18.7 with extension addition absent -}
        encodeSetAuxExt b ms (eb ++ [0]) as xs
encodeSetAuxExt (b1,b2) ms eb (ExtensionAdditionGroup _ a as) (Just x:*:xs)
    = do {- X691REF: 18.7 with extension addition present -}
         {- X691REF: 18.9 with ExtensionAdditionGroup extension -}
         encodeOpen (BuiltinType (SEQUENCE (makeSequence a))) x
         encodeSetAuxExt (b1, Used) ms (eb ++ [1]) as xs
encodeSetAuxExt b ms eb (ExtensionMarker as) xs
    = return (b, eb, encodeSetAux b ms as xs)
encodeSetAuxExt b ms eb EmptySequence Empty
    = return (b, eb, encodeSetAux b ms EmptySequence Empty)
encodeSetAuxExt b odb eb _ _
    = throwError (OtherError "Inappropriate component!")

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
encodeChoiceAux ids@(b, ((f:g:r),e)) (ChoiceOption (NamedType t a) as) (AddAValue x xs)
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

encodeChoiceExtAux :: (NoExtension, (ChoiceRootIndices, ChoiceExtIndices))
                    -> Choice a -> (ExactlyOne a n) -> PERMonad ()
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
                    -> Choice' a -> (ExactlyOne a n) -> PERMonad ()
encodeChoiceExtAux' ids EmptyChoice' _ = throwError (OtherError "No choice value!")
encodeChoiceExtAux' ids ChoiceExtensionMarker' _ = throwError (OtherError "No choice value!")
encodeChoiceExtAux' (b,(r, (f:e))) (ChoiceOption' a as) (AddNoValue x xs) =
   encodeChoiceExtAux' (b, (r,e)) as xs
encodeChoiceExtAux' (b,(r, (f:e))) (ChoiceOption' (NamedType t a) as) (AddAValue x xs)
    = do {- X691REF: 22.5 and 22.8 -}
         oneBit
         encodeNSNNInt (toInteger f) 0
         encodeOpen a x

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

encodeCharInBits :: Integer -> Char -> PERMonad ()
encodeCharInBits i c = toNonNegBinaryInteger (fromInteger . fromIntegral . ord $ c) (fromInteger i)

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

-- The first two cases are described in X.691 27.5.6 and 25.5.7
-- and the last case by 10.9 Note 3.

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

