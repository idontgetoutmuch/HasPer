{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns
#-}

-----------------------------------------------------------------------------
-- |
-- Module      : Language.ASN1.PER.Integer
-- Copyright   : Dominic Steinitz
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Dominic Steinitz <dominic.steinitz@blueyonder.co.uk>
-- Stability   : experimental
--
-- TBD
-----------------------------------------------------------------------------

module GenerateC
   (
     allocPointer
   ) where

import Text.PrettyPrint
import Data.Char

import ASNTYPE

-- | Allocate memory for a variable
allocPointer :: String -> Doc
allocPointer name =
   foldr ($+$) empty [
      text "/* Allocate an instance of " <+> text name <+> text "*/",
      cPtr <> text " = calloc(1, sizeof(" <> cType <> text ")); /* not malloc! */",
      text "assert(" <> cPtr <> text "); /* Assume infinite memory */"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"

lowerFirst :: String -> String
lowerFirst "" = ""
lowerFirst (x:xs) = (toLower x):xs

referenceTypeAndVal :: ASNType a -> a -> Doc
referenceTypeAndVal (ReferencedType r t) v =
   referenceTypeAndValAux1 [(ref r)] t v 
referenceTypeAndVal (ConstrainedType _ _) _ =
   error "I don't know how to create C for a ConstrainedType"
referenceTypeAndVal (BuiltinType b) v =
   error "I don't know how to create C for a BuiltinType"

referenceTypeAndValAux1 :: [Name] -> ASNType a -> a -> Doc
referenceTypeAndValAux1 ns (BuiltinType b) v =
   referenceTypeAndValAux2 ns b v

referenceTypeAndValAux2 :: [Name] -> ASNBuiltin a -> a -> Doc
referenceTypeAndValAux2 ns INTEGER      x = lhs ns <> text " = " <> text (show x) <> semi
referenceTypeAndValAux2 ns (SEQUENCE s) x = cSEQUENCE ns s x

cSEQUENCE = undefined

type Prefix = [Name]

lhs :: Prefix -> Doc
lhs ns = 
   pointer <> components
   where
      (x:xs) = reverse ns
      pointer = parens (text "*" <> text (lowerFirst x))
      components = hcat (map text xs)


