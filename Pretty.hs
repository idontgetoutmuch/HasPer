{-# OPTIONS -fglasgow-exts -Wall -fno-warn-missing-signatures #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  Pretty
-- Copyright   :  (c) Dominic Steinitz 2007
-- License     :  BSD3
--
-- Maintainer  :  dominic.steinitz@blueyonder.co.uk
-- Stability   :  experimental
-- Portability :  portable
--
-- Utilities for prettyprinting ConstrainedTypes
--
-----------------------------------------------------------------------------

module Pretty(
   prettyType
   )  where

import Test.QuickCheck
import Text.PrettyPrint
import Control.Monad.State
import ConstrainedType
import Language.ASN1 hiding (NamedType)
import Data.Char

prettyType :: Show a => ConstrainedType a -> Doc
prettyType INTEGER =
   text "INTEGER"
prettyType(RANGE x l u) =
   let l' = 
         case l of
            Nothing -> text "MIN"
            Just m  -> text (show m)
       u' =
         case u of
            Nothing -> text "MAX"
            Just n  -> text (show n)
   in sep [prettyType x, parens (sep [l',text "..",u'])]
prettyType (SEQUENCE' x) =
   text "SEQUENCE" <> space <> braces (prettyDomSeq x)

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) = 
   prettyType x
prettySeq (Cons x xs) =
   vcat [prettyType x <> comma, prettySeq xs]

prettyElem :: Show a => ElementType a -> Doc
prettyElem (ETMandatory nt) = prettyNamedType nt

prettyNamedType :: Show a => NamedType a -> Doc
prettyNamedType (NamedType n _ ct) =
   text n <> space <> prettyType ct

prettyDomSeq :: DomSequence a -> Doc
prettyDomSeq DomNil =
   empty
prettyDomSeq (DomCons x DomNil) = 
   prettyElem x
prettyDomSeq (DomCons x xs) =
   vcat [prettyElem x <> comma, prettyDomSeq xs]


data RepNamedType = forall t . Show t => RepNamedType (NamedType t)

instance Arbitrary RepNamedType where
   arbitrary =
      do name <- arbitrary
         rct   <- arbitrary
         case rct of
            RepType ct ->
               return (RepNamedType (NamedType (elementName name) Nothing ct))

data RepElementType = forall t . Show t => RepElementType (ElementType t)

instance Arbitrary RepElementType where
   arbitrary =
      do rnt <- arbitrary
         case rnt of
            RepNamedType nt ->
               return (RepElementType (ETMandatory nt)) 

data RepSeq = forall t . Show t => RepSeq (Sequence t)

instance Arbitrary RepSeq where
   arbitrary =
      oneof [
         return (RepSeq Nil),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepType u ->
                  case y of
                     RepSeq v ->
                        return (RepSeq (Cons u v))
         ]

data RepDomSeq = forall t . Show t => RepDomSeq (DomSequence t)

instance Arbitrary RepDomSeq where
   arbitrary =
      oneof [
         return (RepDomSeq DomNil),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u ->
                  case y of
                     RepDomSeq v ->
                        return (RepDomSeq (DomCons u v))
         ]

data RepType = forall t . Show t => RepType (ConstrainedType t)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         return (RepType INTEGER),
         do l <- arbitrary
            u <- suchThat arbitrary (f l)
            return (RepType (RANGE INTEGER l u)),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u -> 
                  case y of
                     RepDomSeq v -> 
                        return (RepType (SEQUENCE' (DomCons u v)))
         ]
      where f l u =
               case l of
                  Nothing -> True
                  Just m  -> case u of
                                Nothing -> True
                                Just n  -> n >= m

instance Show RepType where
   show x =
      case x of
         RepType y ->
            render (prettyType y)

instance Arbitrary TagType where
   arbitrary = 
      oneof [
         return Context,
         return Application
         ]

newtype ElementName = ElementName {elementName :: String}
   deriving Show

instance Arbitrary ElementName where
   arbitrary =
      do first <- suchThat arbitrary isAsciiLower
         rest  <- suchThat arbitrary (and . (map isAsciiLower))
         return (ElementName (first:rest))

main = sample (arbitrary::Gen RepType)
