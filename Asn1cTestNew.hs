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
