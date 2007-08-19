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

pt2 = Range [] (INTEGER []) (Just 3) (Just 6)
ptest2  = SEQUENCE [] (Cons (SEQUENCE [] (Cons pt2 Nil)) Nil)
ptest21 = SEQUENCE [] (Cons pt2 (Cons pt2 Nil))
ptest22 = SEQUENCE [] (Cons pt2 (Cons pt2 (Cons pt2 Nil)))

{-
prettyType :: Show a => ConstrainedType a -> Doc
prettyType (INTEGER _) = text "INTEGER"
prettyType (Range _ x l u) = 
   let l' = 
          case l of
             Nothing -> text "MIN"
             Just m  -> text (show m)
       u' = case u of
               Nothing -> text "MAX"
               Just n  -> text (show n)
       in
    sep [prettyType x, parens (sep [l',text "..",u'])]
prettyType (Includes _ t1 t2) = sep [prettyType t1, parens (prettyType t2)]
prettyType (SEQUENCE _ x) =
   pretty x

{-
prettyRep' :: Rep -> Doc
prettyRep' x =
   case x of
      Rep y ->
         case y of
            INTEGER _ -> 
               text "INTEGER"
            Range _ x l u ->
               let l' = 
                      case l of 
                         Nothing -> text "MIN"
                         Just m  -> text (show m)
                   u' = 
                      case u of
                         Nothing -> text "MAX"
                         Just n  -> text (show n)
               in sep [prettyType x, parens (sep [l',text "..",u'])]
            SEQUENCE _ x -> 
               case x of
                  Cons y ys ->
                     pretty x
-}

{-
data RepSeq = forall a . Show a => RepSeq (Sequence a)

prettySeq :: RepSeq -> Doc
prettySeq x =
   case x of
      RepSeq y ->
         case y of
            Cons x xs -> prettyRep' (Rep x)
-}

class Pretty a where
   pretty :: a -> Doc

instance Pretty (Sequence Nil) where
   pretty _ = empty

instance (Show a, Pretty a, Pretty (Sequence l)) => Pretty (Sequence (a:*:l)) where
   pretty (Cons x xs) = prettyType x <> space <> pretty xs


-- prettyType' (INTEGER _) = text "INTEGER"

{-
prettyType' (SEQUENCE _  xs) = braces (pretty xs)

instance Show (Sequence Nil) where
   show _ = "Nil"

instance (Show a, Show (Sequence l)) => Show (Sequence (a:*:l)) where
   show (Cons x xs) = render (prettyType x) ++ show xs

class Pretty a where
   pretty :: a -> Doc

instance Pretty (Sequence Nil) where
   pretty _ = empty

instance (Show a, Pretty a, Pretty (Sequence l)) => Pretty (Sequence (a:*:l)) where
   pretty (Cons x xs) = prettyType x <> space <> pretty xs

instance Pretty Integer where
   pretty x = text (show x)
-}

{-
prettySeq :: Show a => Sequence a -> Doc
prettySeq Nil = empty
prettySeq (Cons x xs) = prettyType x
-}

{-
prettySeq :: Show a => Sequence a -> Doc
prettySeq Nil = empty
prettySeq (Cons x xs) = sep [prettyType x, comma, prettySeq xs]
-}

data Rep = forall t . Show t => Rep (ConstrainedType t)

instance Arbitrary Rep where
   arbitrary =
      oneof [
         return (Rep (INTEGER [])),
         do l <- arbitrary
            u <- suchThat arbitrary (f l)
            return (Rep (Range [] (INTEGER []) l u))
         ]
      where f l u =
               case l of
                  Nothing -> True
                  Just m  -> case u of
                                Nothing -> True
                                Just n  -> n >= m

prettyRep x =
   case x of
      Rep s ->
         prettyType s 

instance Show Rep where
   show x = render (prettyRep x)

main = sample (arbitrary::Gen Rep)
-}