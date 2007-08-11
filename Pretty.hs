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
prettyType INTEGER = text "INTEGER"
prettyType (Range x l u) = 
   let l' = 
          case l of
             Nothing -> text "MIN"
             Just m  -> text (show m)
       u' = case u of
               Nothing -> text "MAX"
               Just n  -> text (show n)
       in
    sep [prettyType x, parens (sep [l',text "..",u'])]
prettyType (Includes t1 t2) = sep [prettyType t1, parens (prettyType t2)]

data Rep = forall t . Show t => Rep (ConstrainedType t)

instance Arbitrary Rep where
   arbitrary =
      oneof [
         return (Rep INTEGER),
         do l <- arbitrary
            u <- suchThat arbitrary (f l)
            return (Rep (Range INTEGER l u))
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
