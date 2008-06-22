{-# OPTIONS_GHC -XGADTs -fwarn-incomplete-patterns #-}

module NewPretty where

import CTRestruct
import Language.ASN1 (
   TagPlicity (..),
   TagType (..)
   )
import Text.PrettyPrint

prettyType :: ASNType a -> Doc
prettyType (BT bt) = prettyBuiltinType bt
prettyType (ConsT t e) = prettyType t <+> parens (prettyElementSetSpecs t e)

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
   text "CHOICE" <+> braces (prettyChoice c)
prettyBuiltinType (SEQUENCE s) =
   text "SEQUENCE" <> space <> braces (prettySeq s)
prettyBuiltinType (SET s) =
   text "SET" <> space <> braces (prettySeq s)

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

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

prettyPlicity Implicit = text "IMPLICIT"
prettyPlicity Explicit = text "EXPLICIT"

prettyElementSetSpecs t (RE c) = prettyConstraint t c
prettyElementSetSpecs t (EXT c) = prettyConstraint t c <> comma <+> text "..."
prettyElementSetSpecs t (EXTWITH c1 c2) = prettyConstraint t c1 <> comma <+> text "..." <> comma <+> prettyConstraint t c2

prettyConstraint t (UNION u) = prettyUnion t u
prettyConstraint t (ALL e) = prettyExcept t e

prettyExcept t (EXCEPT e) = prettyElem t e

prettyUnion t (IC ic) = prettyIntersectionConstraint t ic
prettyUnion t (UC u i) = prettyUnion t u <+> text "|" <+> prettyIntersectionConstraint t i

prettyIntersectionConstraint t (ATOM ie) = prettyInterSectionElement t ie
prettyIntersectionConstraint t (INTER ic ie) = prettyIntersectionConstraint t ic <+> text "^" <+> prettyInterSectionElement t ie

prettyInterSectionElement t (E e) = prettyElem t e
prettyInterSectionElement t (Exc e exc) = prettyElem t e <+> text "EXCEPT" <+> prettyExclusion t exc

prettyExclusion t (EXCEPT e) = prettyElem t e

prettyElem t (S s) = prettySingleValue t s
prettyElem t (V r) = prettyValueRange t r

prettyValueRange :: ASNType a -> VR a -> Doc
prettyValueRange (BT INTEGER) (R (x,y)) = text (show x) <> text ".." <> text (show y)
prettyValueRange (BT IA5STRING) (R (x,y)) = text (iA5String x) <> text ".." <> text (iA5String y)
prettyValueRange (BT PRINTABLESTRING) (R (x,y)) = text (printableString x) <> text ".." <> text (printableString y)
prettyValueRange (BT NUMERICSTRING) (R (x,y)) = text (numericString x) <> text ".." <> text (numericString y)

prettySingleValue :: ASNType a -> SV a -> Doc
prettySingleValue (BT INTEGER) (SV e) = text (show e)
prettySingleValue (BT (BITSTRING _)) (SV e) = prettyBitString e
prettySingleValue (BT IA5STRING) (SV e) = text (show e)
prettySingleValue (BT PRINTABLESTRING) (SV e) = text (show e)

prettyBitString = (<> text "B") . (quotes . text . concat . map show .  bitString)