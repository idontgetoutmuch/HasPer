{-# OPTIONS_GHC -XGADTs -fwarn-incomplete-patterns #-}

-- -fwarn-incomplete-patterns

module NewPretty where

import ASNTYPE
import PERWriter
import Language.ASN1 (
   -- TagPlicity (..),
   TagType (..)
   )
import Text.PrettyPrint as PP

import NewTestData -- FIXME: For temporary testing - testing should
                   -- really be done outside of the module being tested

prettyType :: ASNType a -> Doc
prettyType (ReferencedType r t) = prettyReferencedType r t
prettyType (BuiltinType bt) = prettyBuiltinType  bt
prettyType (ConstrainedType  (BuiltinType (SEQUENCEOF t)) e) =
   text "SEQUENCE" <+>
   parens (prettyElementSetSpecs undefined e) <+>
   text "OF" <+>
   prettyType t
prettyType (ConstrainedType  t e) =
   prettyType t <+>
   parens (prettyElementSetSpecs t e)

prettySeq :: Sequence a -> Doc
prettySeq EmptySequence =
   PP.empty
prettySeq (AddComponent x EmptySequence) =
   prettyComponentType x
prettySeq (AddComponent x xs) =
   vcat [prettyComponentType x <> comma, prettySeq xs]
prettySeq (ExtensionMarker x) =
   vcat [text "..." <> comma, prettySeq x <> comma]
-- FIXME: What should we do with v?
prettySeq (ExtensionAdditionGroup v x y) =
   vcat [brackets (brackets (prettySeq2 x)) <> comma, prettySeq y]


prettySeq2 :: Sequence' a -> Doc
prettySeq2 EmptySequence' =
   PP.empty
prettySeq2 (AddComponent' x EmptySequence') =
   prettyComponentType x
prettySeq2 (AddComponent' x xs) =
   vcat [prettyComponentType x <> comma, prettySeq2 xs]

prettySeq' :: Sequence a -> [Doc]
prettySeq' EmptySequence =
  []
prettySeq' (AddComponent x xs) =
   (prettyComponentType x):(prettySeq' xs)
prettySeq' (ExtensionMarker x) =
   (text "..."):(prettySeq' x)
-- FIXME: What should we do with v?
prettySeq' (ExtensionAdditionGroup v x y) =
   (brackets (brackets (vcat $ punctuate comma $ prettySeq2' x))):(prettySeq' y)


prettySeq2' :: Sequence' a -> [Doc]
prettySeq2' EmptySequence' =
  []
prettySeq2' (AddComponent' x xs) =
   (prettyComponentType x):(prettySeq2' xs)



prettySeq'' x = vcat $ punctuate comma $ prettySeq' x

prettyComponentType :: ComponentType a -> Doc
prettyComponentType (MandatoryComponent m)   = prettyNamedType m
prettyComponentType (OptionalComponent  m)   = prettyNamedType m <+> text "OPTIONAL"
prettyComponentType (DefaultComponent m@(NamedType _ n) v) = prettyNamedType m <+> text "DEFAULT" <+> prettyTypeVal n v

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
   text "SEQUENCE" <> space <> braces (prettySeq'' s)
prettyBuiltinType (SET s) =
   text "SET" <> space <> braces (prettySeq s)
prettyBuiltinType (SEQUENCEOF t) =
   text "SEQUENCE OF" <+> prettyType t
prettyBuiltinType OCTETSTRING           = text "OCTETSTRING"
prettyBuiltinType (BITSTRING namedBits) = text "BITSTRING" <+> braces (text "FIXME: the named bits")
prettyBuiltinType VISIBLESTRING         = text "VISIBLESTRING"
prettyBuiltinType NUMERICSTRING         = text "NUMERICSTRING"
prettyBuiltinType UNIVERSALSTRING       = text "UNIVERSALSTRING"
prettyBuiltinType BMPSTRING             = text "BMPSTRING"
prettyBuiltinType NULL                  = text "NULL"
prettyBuiltinType (ENUMERATED enums)    = text "ENUMERATED" <+> braces (text "FIXME: the enumeratees")
-- FIXME: For now ignore the tag information
prettyBuiltinType (TAGGED _tagInfo t)    = prettyType t



prettyReferencedType r t = text (ref r) <+> text "::=" <+> prettyType t

prettyChoice :: Choice a -> Doc
prettyChoice EmptyChoice =
   PP.empty
prettyChoice (ChoiceOption nt EmptyChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]
prettyChoice (ChoiceExtensionMarker x) =
   vcat [text "..." <> comma, prettyChoice x <> comma]
-- FIXME: What should we do with v?
prettyChoice (ChoiceExtensionAdditionGroup v x) =
   brackets (brackets (prettyChoice' x))


prettyChoice' :: Choice' a -> Doc
prettyChoice' EmptyChoice' =
   PP.empty
prettyChoice' (ChoiceOption' nt EmptyChoice') =
   prettyNamedType nt
prettyChoice' (ChoiceOption' nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice' xs]
prettyChoice' ChoiceExtensionMarker'  =
   vcat [text "..."]


prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n ct) = text n <+> prettyType ct

prettyPlicity Implicit = text "IMPLICIT"
prettyPlicity Explicit = text "EXPLICIT"

prettyElementSetSpecs t (RootOnly c)
    = prettyConstraint t c
prettyElementSetSpecs t (EmptyExtension c)
    = prettyConstraint t c <> comma <+> text "..."
prettyElementSetSpecs t (NonEmptyExtension c1 c2)
    = prettyConstraint t c1 <> comma <+> text "..." <> comma <+> prettyConstraint t c2

prettyConstraint t (UnionSet u) = prettyUnion t u
prettyConstraint t (ComplementSet e) = prettyExcept t e

prettyExcept t (EXCEPT e) = prettyElem t e

prettyUnion t (NoUnion ic) = prettyIntersectionConstraint t ic
prettyUnion t (UnionMark u i) = prettyUnion t u <+> text "|" <+> prettyIntersectionConstraint t i

prettyIntersectionConstraint t (NoIntersection ie) = prettyInterSectionElement t ie
prettyIntersectionConstraint t (IntersectionMark ic ie) = prettyIntersectionConstraint t ic <+> text "^" <+> prettyInterSectionElement t ie

prettyInterSectionElement t (ElementConstraint e) = prettyElem t e
prettyInterSectionElement t (ExclusionConstraint e exc) = prettyElem t e <+> text "EXCEPT" <+> prettyExclusion t exc

prettyExclusion t (EXCEPT e) = prettyElem t e

prettyElem t (S s) = prettySingleValue t s
prettyElem t (V r) = prettyValueRange t r
prettyElem t (P a) = prettyPermittedAlphabet t a
prettyElem t (C c) = error "C"
prettyElem t (SZ s) = prettySizedElem t s
prettyElem t (IT i) = error "IT"

prettySizedElem :: ASNType a -> SizeConstraint a -> Doc
prettySizedElem t (SC x) = text "SIZE" <+> parens (prettyElementSetSpecs (BuiltinType INTEGER) x)

prettyPermittedAlphabet :: ASNType a -> PermittedAlphabetConstraint a -> Doc
prettyPermittedAlphabet t (FR a) = text "FROM" <+> parens (prettyElementSetSpecs t a)

prettyValueRange :: ASNType a -> ValueRangeConstraint a -> Doc
prettyValueRange (BuiltinType INTEGER) (R (x,y)) = pretty x <> text ".." <> pretty y
prettyValueRange (BuiltinType IA5STRING) (R (x,y)) = text (iA5String x) <> text ".." <> text (iA5String y)
prettyValueRange (BuiltinType PRINTABLESTRING) (R (x,y)) = text (printableString x) <> text ".." <> text (printableString y)
prettyValueRange (BuiltinType NUMERICSTRING) (R (x,y)) = text (numericString x) <> text ".." <> text (numericString y)
prettyValueRange (BuiltinType (BITSTRING _)) (R (x,y)) = text (show x) <> text ".." <> text (show y)

-- FIXME: Everything below is temporary
prettyValueRange (ReferencedType _ _) _          = text "FIXME: prettyValueRange ReferencedType"
prettyValueRange (ConstrainedType _ _) _         = text "FIXME: prettyValueRange ConstrainedType"
prettyValueRange (BuiltinType BOOLEAN) _         = text "FIXME: prettyValueRange BuiltinType BOOLEAN"
prettyValueRange (BuiltinType (ENUMERATED _)) _  = text "FIXME: prettyValueRange BuiltinType ENUMERATED"
prettyValueRange (BuiltinType OCTETSTRING) _     = text "FIXME: prettyValueRange BuiltinType OCTETSTRING"
prettyValueRange (BuiltinType VISIBLESTRING) (R (x, y)) = doubleQuotes (text $ visibleString x) <>
                                                          text ".." <>
                                                          doubleQuotes (text $ visibleString y)
prettyValueRange (BuiltinType UNIVERSALSTRING) _ = text "FIXME: prettyValueRange BuiltinType UNIVERSALSTRING"
prettyValueRange (BuiltinType BMPSTRING) _       = text "FIXME: prettyValueRange BuiltinType BMPSTRING"
prettyValueRange (BuiltinType NULL) _            = text "FIXME: prettyValueRange BuiltinType NULL"
prettyValueRange (BuiltinType (SEQUENCE _)) _    = text "FIXME: prettyValueRange BuiltinType SEQUENCE"
prettyValueRange (BuiltinType (SEQUENCEOF _)) _  = text "FIXME: prettyValueRange BuiltinType SEQUENCEOF"
prettyValueRange (BuiltinType (SET _)) _         = text "FIXME: prettyValueRange BuiltinType SET"
prettyValueRange (BuiltinType (SETOF _)) _       = text "FIXME: prettyValueRange BuiltinType SETOF"
prettyValueRange (BuiltinType (CHOICE _)) _      = text "FIXME: prettyValueRange BuiltinType CHOICE"
prettyValueRange (BuiltinType (TAGGED _ _)) _    = text "FIXME: prettyValueRange BuiltinType TAGGED"



prettySingleValue :: ASNType a -> SingleValueConstraint a -> Doc
prettySingleValue (BuiltinType INTEGER) (SV e) = text (show e)
prettySingleValue (BuiltinType (BITSTRING _)) (SV e) = prettyBitString e
prettySingleValue (BuiltinType IA5STRING) (SV e) = text (show e)
prettySingleValue (BuiltinType PRINTABLESTRING) (SV e) = doubleQuotes (text (printableString e))

-- FIXME: Everything below is temporary
prettySingleValue (ReferencedType _ _) _          = text "FIXME: prettySingleValue ReferencedType"
prettySingleValue (ConstrainedType _ _) _         = text "FIXME: prettySingleValue ConstrainedType"
prettySingleValue (BuiltinType BOOLEAN) _         = text "FIXME: prettySingleValue BOOLEAN"
prettySingleValue (BuiltinType (ENUMERATED _)) _  = text "FIXME: prettySingleValue ENUMERATED"
prettySingleValue (BuiltinType OCTETSTRING) _     = text "FIXME: prettySingleValue OCTETSTRING"
prettySingleValue (BuiltinType VISIBLESTRING) (SV x) = text $ show $ visibleString x
prettySingleValue (BuiltinType NUMERICSTRING) _   = text "FIXME: prettySingleValue NUMERICSTRING"
prettySingleValue (BuiltinType UNIVERSALSTRING) _ = text "FIXME: prettySingleValue UNIVERSALSTRING"
prettySingleValue (BuiltinType BMPSTRING) _       = text "FIXME: prettySingleValue BMPSTRING"
prettySingleValue (BuiltinType NULL) _            = text "FIXME: prettySingleValue NULL"
prettySingleValue (BuiltinType (SEQUENCE _)) _    = text "FIXME: prettySingleValue SEQUENCE"
prettySingleValue (BuiltinType (SEQUENCEOF _)) _  = text "FIXME: prettySingleValue SEQUENCEOF"
prettySingleValue (BuiltinType (SET _)) _         = text "FIXME: prettySingleValue SET"
prettySingleValue (BuiltinType (SETOF _)) _       = text "FIXME: prettySingleValue SETOF"
prettySingleValue (BuiltinType (CHOICE _)) _      = text "FIXME: prettySingleValue CHOICE"
prettySingleValue (BuiltinType (TAGGED _ _)) _    = text "FIXME: prettySingleValue TAGGED"


prettyBitString = (<> text "B") . (quotes . text . concat . map show .  bitString)

class Pretty a where
   pretty :: a -> Doc

instance Pretty InfInteger where
   pretty NegInf = text "MIN"
   pretty PosInf = text "MAX"
   pretty (Val x)  = text (show x)

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal (BuiltinType INTEGER) x = pretty x
prettyTypeVal (BuiltinType (SEQUENCE s)) x = error "SEQUENCE"

prettyElementTypeVal :: ComponentType a -> a -> Doc
prettyElementTypeVal (MandatoryComponent (NamedType n t)) x =
   text n <+> prettyTypeVal t x
