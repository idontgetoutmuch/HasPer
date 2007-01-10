-----------------------------------------------------------------------------
-- |
-- Module      :  Codec.ASN1.BER
-- Copyright   :  (c) Dominic Steinitz 2005
-- License     :  BSD-style (see the file ReadMe.tex)
-- 
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  portable
--
-- Typecheck and decode BER representations as produced by
-- Codec.ASN1.TLV 
--
-----------------------------------------------------------------------------

module Codec.ASN1.BER (
   -- * Types
   Encoding(..),
   Defaulted(..),
   Length,
   -- * Type classes
   Encode(..),
   -- * Function types
   encodedComponents,
   encodedDefComps,
   defaultedTagValue,
   typeCheck,
   replaceRef
	      ) where

import Data.Char
import Data.Bits
import Data.List
import qualified Data.Map as Map
import Control.Monad.Error
import Control.Monad.State
import Codec.Utils
import Codec.ASN1

type Length = Integer
type PrimitiveValue = [Octet]

data Encoding = Primitive TagType TagValue Length PrimitiveValue
              | Constructed TagType TagValue Length [Encoding]
   deriving (Eq,Show)

data Defaulted = DefPrim TagType TagValue Length PrimitiveValue
              | DefCons TagType TagValue Length [Maybe Defaulted]
   deriving (Eq,Show)

encodedComponents :: Encoding -> [Encoding]
encodedComponents (Constructed _ _ _ es) = es

encodedDefComps :: Defaulted -> [Maybe Defaulted]
encodedDefComps (DefCons _ _ _ es) = es

defaultedTagValue :: Defaulted -> TagValue
defaultedTagValue (DefPrim _ t _ _) = t
defaultedTagValue (DefCons _ t _ _) = t

-- | Type check the abstract representation of a Tag Length Value
--   against an ASN.1 type definition.

typeCheck :: TypeDefn -> Encoding -> IO (TypeDefn,Defaulted)

typeCheck a b =
   do ((q,r),_) <- runStateT (tc a b) []
      return (q,r)

tc :: (MonadState [Maybe Encoding] m, MonadError e m) =>
   TypeDefn -> Encoding -> m (TypeDefn,Defaulted)

tc a@(n ::= AbsBasePrim att atv at) b@(Primitive btt btv l bv) 
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | not $ bv `compatibleWith` at = 
        fail ("Checking " ++ (show n) ++ ": " ++
              "type not compatible with values " ++ (show bv))
   | otherwise = return $ (a,DefPrim btt btv l bv)

tc a@(n ::= AbsBasePrim att atv at) b@(Constructed btt btv _ bv) 
   = fail ("Checking " ++ (show n) ++ ": " ++
           "expected PRIMITIVE Tag found CONSTRUCTED Tag" ++
            "\n" ++ (show a) ++ "\n" ++ (show b))

-- See x.690 8.14.2 & 8.14.3

tc (n ::= AbsRef att atv atp at) b@(Primitive btt btv _ bv)
   | atp == Explicit = 
        fail ("Checking " ++ (show n) ++ ": " ++
              "expected IMPLICIT Tag found PRIMITIVE type")
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | otherwise = tc a b
    where a = modName n $ modTagType att $ modTagVal (Just atv) at

tc a'@(n ::= AbsRef att atv atp at) b@(Constructed btt btv bl bvs)
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | otherwise = 
        case atp of
           Implicit -> 
              tc a b
           Explicit -> 
              if null bvs
                 then fail "unable to match empty value"
                 else do (w,x) <- tc at (bvs!!0)
                         let u = DefCons btt btv bl [Just x]
                             v = n ::= AbsRef att atv atp w
                         return $ (v,u)
    where a = modName n $ modTagType att $ modTagVal (Just atv) at

tc (n ::= AbsSeq _ _ _ _) (Primitive _ _ _ _) =
   constructionMismatch n "SEQUENCE" "PRIMITIVE"

tc a@(n ::= AbsSeq att atv atp as) b@(Constructed btt btv l bvs)
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | otherwise = 
        do ((tas,tbvs),s) <- runStateT (k as bvs) []
           return ((n ::= AbsSeq att atv atp tas),(DefCons btt btv l tbvs))

tc (n ::= AbsSeqOf _ _ _ _) (Primitive _ _ _ _) =
   constructionMismatch n "SEQUENCE OF" "PRIMITIVE"

tc a@(n ::= AbsSeqOf att atv Implicit td) b@(Constructed btt btv l bvs)
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | otherwise = do ds <- sequence $ zipWith tc (repeat td) bvs
                    let tbvs = map snd ds
                        ttd  = if null ds then td else head $ map fst ds
                    return (n ::= AbsSeqOf att atv Implicit ttd,DefCons btt btv l (map Just tbvs))

tc (n ::= AbsSetOf _ _ _ _) (Primitive _ _ _ _) =
   constructionMismatch n "SET OF" "PRIMITIVE"

tc (n ::= AbsSetOf att atv Implicit td) (Constructed btt btv l bvs)
   | att /= btt = tagMismatch n att btt
   | atv /= btv = tagValMismatch n atv btv
   | otherwise = do ds <- sequence $ zipWith tc (repeat td) bvs
                    let tbvs = map snd ds
                        ttd  = if null ds then td else head $ map fst ds
                    return (n ::= AbsSetOf att atv Implicit ttd,DefCons btt btv l (map Just tbvs))

tc (n ::= AbsAnyDefBy i) b =
   do s <- get
      let t = reverse s
      if ((t!!i) == Nothing)
         then fail ("Checking " ++ (show n) ++ ": " ++
                     "no optional value present in ANY DEFINED BY")
         else do let (Just x) = t!!i
                 (_,y) <- tc absOID x
                 let u = (decode (getAbsType absOID) (Just y))::(Maybe OID)
                     (Just u') = u
                     v = Map.lookup u' oids
                 if v == Nothing 
                    then fail ("Checking " ++ (show n) ++ ": " ++
                               (show u) ++ " not supported")
                    else do let (Just w) = v
                            foo <- tc w b
                            return foo

tc (n ::= AbsChoice tpnts) b =
   foldr ignoreErr 
         (fail (choiceFailMsg n b))
         (map ((flip choiceAux) b) tpnts)

ignoreErr :: MonadError e m => m a -> m a -> m a
ignoreErr m n = m `catchError` (\_ -> n)

choiceFailMsg n b =
   "Checking " ++ 
   (show n) ++ 
   ": " ++
   "no CHOICE alternative matches " ++
    (show b)

choiceAux :: (MonadState [Maybe Encoding] m, MonadError e m) =>
   (TagPlicity,NamedType) -> Encoding -> m (TypeDefn,Defaulted)
--    TypeDefn -> Encoding -> m (TypeDefn,Defaulted)

choiceAux (tp,nt) b =
   do let (mn :>: (mt :@: td)) = nt
      case mn of
         Nothing ->
            fail ("expected identifier " ++
                  "(beginning with a lower-case letter): " ++
                  "this identifier is mandatory since ASN.1:1994")
         Just n -> 
            case tp of
               Implicit ->
                  case mt of
                     Nothing ->
                        tc (modName n td) b
                     Just t ->
                        tc (modName n $ modTagType Context $ modTagVal mt td) b
               Explicit ->
                  case mt of
                     Nothing -> 
                        fail "tag expected before EXPLICIT"
                     Just t ->
                        tc (n ::= AbsRef Context t Explicit td) b

k :: (MonadState [Maybe Encoding] m, MonadError e m) =>
   [ComponentType] -> [Encoding] -> 
      StateT [Maybe Encoding] m ([ComponentType],[Maybe Defaulted])

k [] [] = return ([],[])

k [] _  = return ([],[])

k ((a@(Regular _)):_) []  = 
   fail ("Checking " ++ (show a) ++ ": " ++ "insufficient components")

k (a@(AnyDefBy n):as) [] =
   fail ("Checking " ++ (show a) ++ ": " ++ "insufficient components")

k a@(Optional _:_) [] = return (a,[Nothing])

k (Default _ _:_) [] = fail "To be fixed"

k (Regular (mn :>: (tv :@: td)):as) (bv:bvs) = 
   do s <- get
      let inner = 
             do put s
                case tv of
                   Nothing ->
                      tc td bv
                   Just v ->
                      case mn of
-- 29/01/05 082427 Consider replacing Maybe String by String.
-- If there is no name then it's the empty String "".
                         Nothing ->
                            tc ("" ::= AbsRef Context v Implicit td) bv
                         Just name ->
                            tc (name ::= AbsRef Context v Implicit td) bv
      (ttd,tbv) <- lift $ inner
      let tct = Regular (mn :>: (tv :@: ttd))
      put (Just bv:s)
      (tcts,tbvs) <- k as bvs
      return (tct:tcts,(Just tbv):tbvs)

k (a@(Optional (mn :>: (tv :@: td))):as) b@(bv:bvs) = 
-- For the moment. We don't want to catch all errors. For example,
-- if we get an eof error then it should be propogated.
   do s <- get
      let inner =
             do put s
                case tv of
                   Nothing ->
                      tc td bv
                   Just v ->
                      case mn of
-- 29/01/05 082427 Consider replacing Maybe String by String.
-- If there is no name then it's the empty String "".
                         Nothing ->
	                    tc ("" ::= AbsRef Context v Implicit td) bv
                         Just name ->
                            tc (name ::= AbsRef Context v Implicit td) bv
      maybeOption <- 
         (do foo <- lift $ inner 
             return (Just foo)) `catchError`
         (\_ -> return Nothing)
      case maybeOption of
         Nothing ->
            do put (Nothing:s)
               (tcts,tbvs) <- k as b
               return (a:tcts,Nothing:tbvs)
         Just (ttd,tbv) ->
            do s <- get
               put (Just bv:s)
               (tcts,tbvs) <- k as bvs
               let tct = Optional (mn :>: (tv :@: ttd))
               return (tct:tcts,(Just tbv):tbvs)

k (a@(Default (mn :>: (tv :@: td)) _):as) b@(bv:bvs) = 
-- For the moment. We don't want to catch all errors. For example,
-- if we get an eof error then it should be propogated.
   do s <- get
      let inner =
             do put s
                case tv of
                   Nothing ->
                      tc td bv
                   Just v ->
                      case mn of
-- 29/01/05 082427 Consider replacing Maybe String by String.
-- If there is no name then it's the empty String "".
                         Nothing ->
	                    tc ("" ::= AbsRef Context v Implicit td) bv
                         Just name ->
                            tc (name ::= AbsRef Context v Implicit td) bv
      maybeOption <- 
         (do foo <- lift $ inner 
             return (Just foo)) `catchError`
         (\_ -> return Nothing)
      case maybeOption of
         Nothing ->
            do put (Nothing:s) -- This is wrong. We should insert the default.
               (tcts,tbvs) <- k as b
               return (a:tcts,Nothing:tbvs)
         Just (ttd,tbv) ->
            do s <- get
               put (Just bv:s)
               (tcts,tbvs) <- k as bvs
               let tct = Optional (mn :>: (tv :@: ttd))
               return (tct:tcts,(Just tbv):tbvs)

k ((AnyDefBy n):as) (bv:bvs) =
   do s <- get
      if ((s!!n) == Nothing)
         then fail ("Checking " ++ (show n) ++ ": " ++
                     "no optional value present in ANY DEFINED BY")
         else do let (Just x) = (reverse s)!!n
                 (_,y) <- lift $ tc absOID x
                 let u = decode (getAbsType absOID) (Just y)
                     (Just u') = u
                     v = Map.lookup u' oids
                 if v == Nothing 
                    then fail ("Checking " ++ (show n) ++ ": " ++
                               (show u) ++ " not supported")
                    else do let (Just w) = v
                            (ttd,tbv) <- lift $ tc w bv
                            s <- get
                            put (Just bv:s)
                            (tcts,tbvs) <- k as bvs
                            -- We didn't capture all the relevant
                            -- information in the AnyDefBy constructor
                            -- so this is all we can do for the moment.
                            let tct = Regular (Nothing :>: (Nothing :@: ttd))
                            return (tct:tcts,(Just tbv):tbvs)

compatibleWith :: PrimitiveValue -> AbsPrimType -> Bool
compatibleWith pv AbsVisibleString = 
   all (flip elem visibleOctets) pv
compatibleWith pv AbsPrintableString =
   all (flip elem printableOctets) pv
compatibleWith pv AbsIA5String =
   all (flip elem ia5Octets) pv   
compatibleWith pv AbsBool = 
   length pv == 1 
compatibleWith pv AbsInteger =
   if length pv > 1
      then not ((pv!!0 == 0xff && (testBit (pv!!1) msb)) ||
                (pv!!0 == 0x00 && (not (testBit (pv!!1) msb))))
      else length pv == 1
compatibleWith pv AbsOID = not $ null pv
compatibleWith pv AbsOctetString = True
compatibleWith pv AbsBitString = True
compatibleWith pv AbsNull = null pv

ia5Octets :: [Octet]
ia5Octets = [0..127]

visibleOctets :: [Octet]
visibleOctets = map fromIntegral [ord ' '..ord '~']

printableOctets :: [Octet]
printableOctets = 
   map (fromIntegral . ord) printableString

printableString =
   ['A'..'Z'] ++
   ['0'..'9'] ++
   [' ']      ++
   ['a'..'z'] ++
   ['\'']     ++
   ['(']      ++
   [')']      ++
   ['+']      ++
   [',']      ++
   ['-']      ++
   ['.']      ++
   ['/']      ++
   [':']      ++
   ['=']      ++
   ['?'] 

tagMismatch n a b =
   fail ("Checking " ++ (show n) ++ ": " ++
         "expected tag type " ++ (show a) ++ " " ++
         "found tag type " ++ (show b))

tagValMismatch n a b =
   fail ("Checking " ++ (show n) ++ ": " ++
         "expected tag value " ++ (show a) ++ " " ++
         "found tag value " ++ (show b))

constructionMismatch n sa sb = 
   fail ("Checking " ++ (show n) ++ ": " ++
         "unable to match " ++ sa ++ " with " ++ sb)

decodeMismatch a b =
   fail ("Panic: unable to decode " ++ (show b) ++ " with " ++ (show a)) 

class Encode a where
   decode :: AbstractType -> Maybe Defaulted -> Maybe a

instance Encode VisibleString where
   decode a{-@(AbsBasePrim _ _ AbsVisibleString)-} b = 
      case a of
         AbsBasePrim _ _ AbsVisibleString ->
            do x <- b
               case x of
                  DefPrim _ _ _ bv ->
                     return $ VisibleString $ map (chr . fromIntegral) bv
                  _ ->
                     decodeMismatch a b
         _ ->
            error (show a) 

instance Encode PrintableString where
   decode a@(AbsBasePrim _ _ AbsPrintableString) b = 
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return $ PrintableString $ map (chr . fromIntegral) bv
            _ ->
               decodeMismatch a b

instance Encode IA5String where
   decode a@(AbsBasePrim _ _ AbsIA5String) b = 
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return $ IA5String $ map (chr . fromIntegral) bv
            _ ->
               decodeMismatch a b

instance Encode DirectoryString where
   decode a@(AbsBasePrim _ _ AbsIA5String) b = 
      do x <- decode a b
         return (IA x)
   decode a@(AbsBasePrim _ _ AbsPrintableString) b = 
      do x <- decode a b      
         return (PS x)
   decode a@(AbsBasePrim _ _ AbsVisibleString) b = 
      do x <- decode a b      
         return (VS x)

instance Encode Bool where
   decode a@(AbsBasePrim _ _ AbsBool) b =
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               case bv of
                  [0x00]    -> return False
                  otherwise -> return True
            _ ->
               decodeMismatch a b

instance Encode Integer where
   decode a@(AbsBasePrim _ _ AbsInteger) b =
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return (fromTwosComp bv)
            _ ->
               decodeMismatch a b         

instance Encode OctetString where
   decode a@(AbsBasePrim _ _ AbsOctetString) b =
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return $ OctetString bv      
            _ ->
               decodeMismatch a b

instance Encode BitString where
   decode a@(AbsBasePrim _ _ AbsBitString) b =
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return $ BitString (tail bv) 
-- For now. Typechecking will have to ensure this is valid.   
            _ ->
               decodeMismatch a b

instance Encode a => Encode (SetOf a) where
   decode a b = 
      do d <- b
         let bs = encodedDefComps d
         cs <- f a' bs
         return $ SetOf cs
      where a' = absSetOfType a
            f x ys = 
               case ys of
                  [] ->
                     return $ []
                  (z:zs) ->
                     do u <- decode x z
                        us <- f x zs
                        return $ (u:us) 

instance Encode a => Encode [a] where
   decode a b = 
      do d <- b
         let bs = encodedDefComps d
         cs <- f a' bs
         return cs
      where a' = absSeqOfType a
            f x ys = 
               case ys of
                  [] ->
                     return $ []
                  (z:zs) ->
                     do u <- decode x z
                        us <- f x zs
                        return $ (u:us) 

instance Encode OID where
   decode a@(AbsBasePrim _ _ AbsOID) b =
      do x <- b
         case x of
            DefPrim _ _ _ bv ->
               return $ decodeOIDAux bv
            _ ->
               decodeMismatch a b

decodeOIDAux (x:xs) = 
   OID $ ((fromIntegral x) `div` 40):((fromIntegral x) `mod` 40):ys
      where
         ys = map fromIntegral $
	      map (fromOctets (2^oidBitsPerOctet)) $
	      (map . map) (flip clearBit oidBitsPerOctet) (subIds xs)
         subIds :: [Octet] -> [[Octet]]
         subIds = unfoldr getSubId
         getSubId :: [Octet] -> Maybe ([Octet], [Octet])
         getSubId [] = Nothing
         getSubId xs = Just $ span' endOfSubId xs
         endOfSubId = not . (flip testBit oidBitsPerOctet)

oidBitsPerOctet = 7 :: Int

span' :: (a -> Bool) -> [a] -> ([a],[a])
span' p []
   = ([],[])
span' p xs@(x:xs') 
   | p x       = ([x],xs') 
   | otherwise = (x:ys,zs)
      where (ys,zs) = span' p xs'

replaceRef :: AbstractType -> 
              [AbstractType] -> 
              [Maybe Defaulted] -> 
              AbstractType
replaceRef a as bs = 
   case a of
      AbsAnyDefBy n -> u
         where
            oidat = decode (as!!n) (bs!!n)
            (Just oidat') = oidat
            t     = Map.lookup oidat' oids
            (Just (_ ::= u)) = t
      _ -> a
