module Pretty(
   prettyType,
   prettyTypeVal,
   pretty,
   prettyVal
   )  where

import Text.PrettyPrint
import ConstrainedType

prettyConstraint :: (Ord a, Show a) => Constraint a -> Doc
prettyConstraint (Elem s) = text (show s)

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
   text "BITSTRING"
prettyType INTEGER =
   text "INTEGER"
prettyType(RANGE x l u) =
   prettyType x <+> outer x l u
prettyType (SEQUENCE x) =
   text "SEQUENCE" <> space <> braces (prettySeq x)
prettyType (CHOICE xs) =
   text "CHOICE" <+> braces (prettyChoice xs)
prettyType(SIZE t s _) =
   prettyType t <+> parens (text "SIZE" <+> prettyConstraint s) -- text (show s))

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal a@(BITSTRING []) x     = text (show x)
prettyTypeVal a@INTEGER x       = text (show x)
prettyTypeVal a@(RANGE t l u) x = prettyTypeVal t x
prettyTypeVal a@(SIZE t s e) x  = prettyTypeVal t x
prettyTypeVal a@(SEQUENCE s) x  = braces (prettySeqVal s x)

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

prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n _ ct) =
   text n <+> prettyType ct

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys

instance Eq (HL Nil (S Z)) where
   _ == _ = True

instance (Eq a, Eq (HL l (S Z))) => Eq (HL (a:*:l) (S Z)) where
   ValueC   _ _ == NoValueC _ _ = False
   NoValueC _ _ == ValueC _ _   = False
   NoValueC _ xs == NoValueC _ ys = xs == ys
   ValueC x _ == ValueC y _ = x == y
