\documentclass{article}
%include polycode.fmt
\begin{document}

\section{Introduction}
Some notes:

\begin{enumerate}

\item
ASN.1 is an abstract way of representing data and concrete representations (in terms of bits).
\item
We represent ASN.1 as an Abstract Syntax Tree.
This can either be displayed as the original ASN.1 or it can be displayed as a DTD
(I think this is possible --- that's what asn1c can do).
It's also possible to display it as C code which uses asn1c (http://lionet.info/asn1c).
\end{enumerate}

\section{Test Strategy}
\begin{enumerate}
\item
Download and install the asn1c software.
\item
Create some ASN.1 types using the Haskell AST.
\item
Run Pretty.hs to format them as ASN.1.
\item
Run asn1c to generate the C code to handle those ASN.1 types.
\item
Run Asn1cTest.hs to generate a C program which encodes values of the ASN.1 types.
\item
Compile and run the C program. This will encode some values.
\item
Run Test.lhs with the ASN.1 types to decode the values encoded with the C program.
These should be the values you first thought of.
\end{enumerate}

\section{The Code}

\begin{code}
module Pretty(
   prettyType,
   prettyTypeVal
   )  where

import Text.PrettyPrint
import ConstrainedType

prettyConstraint :: (Ord a, Show a) => Constraint a -> Doc
prettyConstraint (Elem s) = text (show s)

class Pretty a where
   pretty :: a -> Doc

instance Pretty (ASNType a) where
   pretty = prettyType

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
\end{code}

\begin{code}

instance Pretty (Sequence a) where
   pretty = prettySeq

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

prettyElem :: ElementType a -> Doc
prettyElem (ETMandatory nt) = prettyNamedType nt

prettyElementTypeVal :: ElementType a -> a -> Doc
prettyElementTypeVal (ETMandatory (NamedType n _ t)) x =
   text n <+> prettyTypeVal t x

instance Pretty (Choice a) where
   pretty = prettyChoice

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

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

\end{code}

\end{document}
