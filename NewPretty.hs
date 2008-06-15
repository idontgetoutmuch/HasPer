{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module NewPretty where

import CTRestruct
import Text.PrettyPrint

prettyElementSetSpecs (RE c) = prettyConstraint c
prettyElementSetSpecs (EXT c) = prettyConstraint c <> comma <+> text "..."
prettyElementSetSpecs (EXTWITH c1 c2) = prettyConstraint c1 <> comma <+> text "..." <> comma <+> prettyConstraint c2

prettyConstraint (UNION u) = prettyUnion u
prettyConstraint (ALL e) = prettyExcept e

prettyExcept (EXCEPT e) = prettyElem e

prettyUnion (IC ic) = prettyIntersectionConstraint ic
prettyUnion (UC u i) = prettyUnion u <+> text "|" <+> prettyIntersectionConstraint i

prettyIntersectionConstraint (ATOM ie) = prettyInterSectionElement ie
prettyIntersectionConstraint (INTER ic ie) = prettyIntersectionConstraint ic <+> text "^" <+> prettyInterSectionElement ie

prettyInterSectionElement (E e) = prettyElem e
prettyInterSectionElement (Exc e exc) = prettyElem e <+> text "EXCEPT" <+> prettyExclusion exc

prettyExclusion (EXCEPT e) = prettyElem e

prettyElem (S s) = prettySingleValue s
prettyElem (V r) = prettyValueRange r

prettyValueRange (R (x,y)) = text (show x) <> text ".." <> text (show y)

prettySingleValue (SV e) = text (show e)
