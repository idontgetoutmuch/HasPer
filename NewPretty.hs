{-# OPTIONS_GHC -XGADTs #-}

-- -fwarn-incomplete-patterns

module NewPretty where

import ASNTYPE
import CTRestruct
import Language.ASN1 (
   TagPlicity (..),
   TagType (..)
   )
import Text.PrettyPrint

prettyType :: ASNType a -> Doc
prettyType (BT bt) = prettyBuiltinType bt
prettyType (ConsT (BT (SEQUENCEOF t)) e) =
   text "SEQUENCE" <+> 
   parens (prettyElementSetSpecs undefined e) <+> 
   text "OF" <+> 
   prettyType t
prettyType (ConsT t e) = 
   prettyType t <+> 
   parens (prettyElementSetSpecs t e)

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) =
   prettyComponentType x
prettySeq (Cons x xs) =
   vcat [prettyComponentType x <> comma, prettySeq xs]

prettyComponentType :: ComponentType a -> Doc
prettyComponentType (CTMandatory m) = prettyNamedType m
prettyComponentType (CTOptional m ) = prettyNamedType m <+> text "OPTIONAL"

prettyBuiltinType :: ASNBuiltin a -> Doc
prettyBuiltinType (BITSTRING []) =
   text "BIT STRING"
prettyBuiltinType INTEGER =
   text "INTEGER"
prettyBuiltinType PRINTABLESTRING =
   text "PrintableString"
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
prettyBuiltinType (SEQUENCEOF t) =
   text "SEQUENCE OF" <+> prettyType t

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n (BT (TAGGED (tt,tv,tp) t))) =
         case tt of
            Context ->
               text n <+> brackets (text (show tv)) <+> prettyPlicity tp <+> prettyType t
            _ ->
               text n <+> brackets (text (show tt) <+> text (show tv)) <+> prettyPlicity tp <+> prettyType t
prettyNamedType (NamedType n ct) = prettyType ct



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
prettyElem t (P a) = prettyPermittedAlphabet t a
prettyElem t (C c) = error "C"
prettyElem t (SZ s) = prettySizedElem t s
prettyElem t (IT i) = error "IT"

prettySizedElem :: ASNType a -> Sz a -> Doc
prettySizedElem t (SC x) = text "SIZE" <+> parens (prettyElementSetSpecs (BT INTEGER) x)

prettyPermittedAlphabet :: ASNType a -> PA a -> Doc
prettyPermittedAlphabet t (FR a) = text "FROM" <+> parens (prettyElementSetSpecs t a)

prettyValueRange :: ASNType a -> VR a -> Doc
prettyValueRange (BT INTEGER) (R (x,y)) = pretty x <> text ".." <> pretty y
prettyValueRange (BT IA5STRING) (R (x,y)) = text (iA5String x) <> text ".." <> text (iA5String y)
prettyValueRange (BT PRINTABLESTRING) (R (x,y)) = text (printableString x) <> text ".." <> text (printableString y)
prettyValueRange (BT NUMERICSTRING) (R (x,y)) = text (numericString x) <> text ".." <> text (numericString y)
prettyValueRange (BT (BITSTRING _)) (R (x,y)) = text (show x) <> text ".." <> text (show y)

prettySingleValue :: ASNType a -> SV a -> Doc
prettySingleValue (BT INTEGER) (SV e) = text (show e)
prettySingleValue (BT (BITSTRING _)) (SV e) = prettyBitString e
prettySingleValue (BT IA5STRING) (SV e) = text (show e)
prettySingleValue (BT PRINTABLESTRING) (SV e) = doubleQuotes (text (printableString e))

prettyBitString = (<> text "B") . (quotes . text . concat . map show .  bitString)

class Pretty a where
   pretty :: a -> Doc

instance Pretty InfInteger where
   pretty NegInf = text "MIN"
   pretty PosInf = text "MAX"
   pretty (Val x)  = text (show x)

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal (BT INTEGER) x = pretty x


prettyElementTypeVal :: ComponentType a -> a -> Doc
prettyElementTypeVal (CTMandatory (NamedType n t)) x =
   text n <+> prettyTypeVal t x
