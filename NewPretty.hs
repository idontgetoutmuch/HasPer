{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module NewPretty where

import CTRestruct
import Language.ASN1 (
   TagPlicity (..),
   TagType (..)
   )
import Text.PrettyPrint

prettyType :: ASNType a -> Doc
prettyType (BT bt) = prettyBuiltinType bt

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) =
   prettyComponentType x
prettySeq (Cons x xs) =
   vcat [prettyComponentType x <> comma, prettySeq xs]

prettyComponentType :: ComponentType a -> Doc
prettyComponentType (CTMandatory m) = prettyNamedType m

prettyBuiltinType :: ASNBuiltin a -> Doc
prettyBuiltinType (BITSTRING []) =
   text "BIT STRING"
prettyBuiltinType INTEGER =
   text "INTEGER"
prettyBuiltinType BOOLEAN =
   text "BOOLEAN"
prettyBuiltinType IA5STRING =
   text "IA5STRING"
prettyBuiltinType (CHOICE c) =
   prettyChoice c
prettyBuiltinType (SEQUENCE s) =
   prettySeq s

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

prettyPlicity :: TagPlicity -> Doc
prettyPlicity Implicit = text "IMPLICIT"
prettyPlicity Explicit = text "EXPLICIT"

prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n ti ct) =
   case ti of
      Nothing ->
         text n <+> prettyType ct
      Just (tt, tv, tp) ->
         case tt of
            Context ->
               text n <+> brackets (text (show tv)) <+> prettyPlicity tp <+> prettyType ct
            _ ->
               text n <+> brackets (text (show tt) <+> text (show tv)) <+> prettyPlicity tp <+> prettyType ct

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
