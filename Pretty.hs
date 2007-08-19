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

prettyType :: Show a => ConstrainedType a -> Doc
prettyType (INTEGER _) =
   text "INTEGER"
prettyType(Range _ x l u) =
   let l' = 
         case l of
            Nothing -> text "MIN"
            Just m  -> text (show m)
       u' =
         case u of
            Nothing -> text "MAX"
            Just n  -> text (show n)
   in sep [prettyType x, parens (sep [l',text "..",u'])]
prettyType (SEQUENCE _ x) =
   text "SEQUENCE" <> space <> braces (prettySeq x)

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) = 
   prettyType x
prettySeq (Cons x xs) =
   vcat [prettyType x <> comma, prettySeq xs]

pt1     = INTEGER []
ptest1  = SEQUENCE [] (Cons (SEQUENCE [] (Cons pt1 Nil)) Nil)
ptest11 = SEQUENCE [] (Cons pt1 (Cons pt1 Nil))
ptest12 = SEQUENCE [] (Cons pt1 (Cons pt1 (Cons pt1 Nil)))

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

data RepType = forall t . Show t => RepType (ConstrainedType t)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         return (RepType (INTEGER [])),
         do l <- arbitrary
            u <- suchThat arbitrary (f l)
            return (RepType (Range [] (INTEGER []) l u)),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepType u -> 
                  case y of
                     RepSeq v -> 
                        return (RepType (SEQUENCE [] (Cons u v)))
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

main = sample (arbitrary::Gen RepType)
