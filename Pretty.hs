module Pretty(
   prettyType,
   prettyTypeVal,
   pretty,
   prettyVal
   )  where

import Text.PrettyPrint
import ConstrainedType
import Language.ASN1 (TagType(..), TagPlicity(..))

prettyConstraint :: Constraint -> Doc
prettyConstraint (Elem s) = let (x,y) = s in parens (text (show x) <> text ".." <> text (show y)) -- WARNING for now - Dan is changing
prettyConstraint (Union c1 c2) = parens (prettyConstraint c1 <+> text "|" <+> prettyConstraint c2)
prettyConstraint (Intersection c1 c2) = parens (prettyConstraint c1 <+> text "^" <+> prettyConstraint c2)
prettyConstraint (Except c1 c2) = parens (prettyConstraint c1 <+> text "EXCEPT" <+> prettyConstraint c2)

class Pretty a where
   pretty :: a -> Doc

class PrettyVal a b where
   prettyVal :: a -> b -> Doc

instance Pretty (ASNType a) where
   pretty = prettyType

instance PrettyVal (ASNType a) a where
   prettyVal = prettyTypeVal

prettyType :: ASNType a -> Doc
prettyType (TYPEASS tr _ t) =
   text tr <+> text "::=" <+> prettyType t
prettyType (BITSTRING []) =
   text "BIT STRING"
prettyType INTEGER =
   text "INTEGER"
prettyType BOOLEAN =
   text "BOOLEAN"
prettyType(RANGE x l u) =
   prettyType x <+> outer x l u
prettyType (SEQUENCE x) =
   text "SEQUENCE" <> space <> braces (prettySeq x)
prettyType (CHOICE xs) =
   text "CHOICE" <+> braces (prettyChoice xs)
prettyType(SIZE t s _) =
   prettyType t <+> parens (text "SIZE" <+> prettyConstraint s) -- text (show s))

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal a@(BITSTRING []) x     = prettyBitString x
prettyTypeVal a@INTEGER x       = text (show x)
prettyTypeVal a@(RANGE t l u) x = prettyTypeVal t x
prettyTypeVal a@(SIZE t s e) x  = prettyTypeVal t x
prettyTypeVal a@(SEQUENCE s) x  = braces (prettySeqVal s x)
prettyTypeVal a@(CHOICE c) x = prettyChoiceVal c x

outer :: ASNType a -> Maybe a -> Maybe a -> Doc
outer INTEGER Nothing  Nothing  = parens (text "MIN"    <> text ".." <> text "MAX")
outer INTEGER Nothing (Just y)  = parens (text "MIN"    <> text ".." <> text (show y))
outer INTEGER (Just x) Nothing  = parens (text (show x) <> text ".." <> text "MAX")
outer INTEGER (Just x) (Just y) = parens (text (show x) <> text ".." <> text (show y))
outer (RANGE t l u) x y = outer t x y

instance Pretty (Sequence a) where
   pretty = prettySeq

instance PrettyVal (Sequence a) a where
   prettyVal = prettySeqVal

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) =
   prettyElem x
prettySeq (Cons x xs) =
   vcat [prettyElem x <> comma, prettySeq xs]

prettySeqVal :: Sequence a -> a -> Doc
prettySeqVal Nil _ = empty
prettySeqVal (Cons e Nil) (x:*:Empty) =
   prettyElementTypeVal e x
prettySeqVal (Cons e l) (x:*:xs) =
   prettyElementTypeVal e x <> comma $$ prettySeqVal l xs

instance Pretty (ElementType a) where
   pretty = prettyElem

instance PrettyVal (ElementType a) a where
   prettyVal = prettyElementTypeVal

prettyElem :: ElementType a -> Doc
prettyElem (ETMandatory nt) = prettyNamedType nt

prettyElementTypeVal :: ElementType a -> a -> Doc
prettyElementTypeVal (ETMandatory (NamedType n _ t)) x =
   text n <+> prettyTypeVal t x

instance Pretty (Choice a) where
   pretty = prettyChoice

instance PrettyVal (Choice a) (HL a (S Z)) where
   prettyVal = prettyChoiceVal

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

prettyChoiceVal :: Choice a -> (HL a (S Z)) -> Doc
prettyChoiceVal NoChoice _ = empty
prettyChoiceVal (ChoiceOption (NamedType n i t) cs) (NoValueC NoValue vs) =
   prettyChoiceVal cs vs
prettyChoiceVal (ChoiceOption (NamedType n i t) cs) (ValueC v vs) =
   text n <> colon <> prettyTypeVal t v

instance Pretty (NamedType a) where
   pretty = prettyNamedType

{-
[UNIVERSAL 29]   tag-value 29, "universal" class
[APPLICATION 10] tag-value 10, "application" class
[PRIVATE 0]      tag-value 0,  "private" class
[3]              tag-value 3,  "context-specific" class

integer1 INTEGER ::= 72
integer2 [1] IMPLICIT INTEGER ::= 72
integer3 [APPLICATION 27] EXPLICIT INTEGER ::= 72
-}

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

prettyBitString = (<> text "B") . (quotes . text . concat . map show .  bitString)