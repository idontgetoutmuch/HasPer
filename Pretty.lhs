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

\begin{code}
module Pretty(
   prettyType
   )  where

import Test.QuickCheck
import Text.PrettyPrint
import Control.Monad.State
import ConstrainedType
import Language.ASN1 hiding (NamedType)
import Data.Char
import Data.Maybe

prettyType :: Show a => ASNType a -> Doc
prettyType INTEGER =
   text "INTEGER"
prettyType(RANGE x l u) =
   let l' = 
         case l of
            Nothing -> text "MIN"
            Just m  -> text (show m)
       u' =
         case u of
            Nothing -> text "MAX"
            Just n  -> text (show n)
   in sep [prettyType x, parens (sep [l',text "..",u'])]
prettyType (SEQUENCE x) =
   text "SEQUENCE" <> space <> braces (prettySeq x)

prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) = 
   prettyElem x
prettySeq (Cons x xs) =
   vcat [prettyElem x <> comma, prettySeq xs]

prettyElem :: Show a => ElementType a -> Doc
prettyElem (ETMandatory nt) = prettyNamedType nt

prettyNamedType :: Show a => NamedType a -> Doc
prettyNamedType (NamedType n _ ct) =
   text n <> space <> prettyType ct

data RepNamedType = forall t . Show t => RepNamedType (NamedType t)

instance Arbitrary RepNamedType where
   arbitrary =
      do name <- arbitrary
         rct   <- arbitrary
         case rct of
            RepType ct ->
               return (RepNamedType (NamedType (elementName name) Nothing ct))

data RepElementType = forall t . Show t => RepElementType (ElementType t)

instance Arbitrary RepElementType where
   arbitrary =
      do rnt <- arbitrary
         case rnt of
            RepNamedType nt ->
               return (RepElementType (ETMandatory nt)) 

data RepSeq = forall t . Show t => RepSeq (Sequence t)

instance Arbitrary RepSeq where
   arbitrary =
      oneof [
         return (RepSeq Nil),
         do x <- arbitrary
            y <- arbitrary
            e <- arbitrary
            case x of
               RepType u ->
                  case y of
                     RepSeq v ->
                        return (RepSeq (Cons (ETMandatory (NamedType (elementName e) Nothing u)) v))
         ]

data RepType = forall t . Show t => RepType (ASNType t)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         return (RepType INTEGER),
         do l <- arbitrary
            u <- suchThat arbitrary (f l)
            return (RepType (RANGE INTEGER l u)),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u -> 
                  case y of
                     RepSeq v -> 
                        return (RepType (SEQUENCE (Cons u v)))
         ]
      where f l u =
               case l of
                  Nothing -> True
                  Just m  -> case u of
                                Nothing -> True
                                Just n  -> n >= m

instance Show RepType where
   show x =
      case x of
         RepType y ->
            render (prettyType y)

data RepValue = forall t . Show t => RepValue (ASNType t) t

instance Arbitrary RepValue where
   arbitrary =
      oneof [
         do x <- arbitrary
            return (RepValue INTEGER x),
         do l <- arbitrary
            u <- suchThat arbitrary (fromMaybe True . (f l))
            x <- suchThat (suchThat arbitrary (fromMaybe True . (h1 l))) (fromMaybe True . (h2 u))
            return (RepValue (RANGE INTEGER l u) x)
{-
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u -> 
                  case y of
                     RepSeq v -> 
                        return (RepType (SEQUENCE (Cons u v)))
-}
         ]
      where f l u =
               do m <- l
                  n <- u
                  return (n >= m)
            h1 l x = l >>= \m -> return (x >= m)
            h2 u x = u >>= \n -> return (x <= n)
               

instance Show RepValue where
   show x =
      case x of
         RepValue t x ->
            render (prettyType t) ++ ": " ++ show x

instance Arbitrary TagType where
   arbitrary = 
      oneof [
         return Context,
         return Application
         ]

newtype ElementName = ElementName {elementName :: String}
   deriving Show

instance Arbitrary ElementName where
   arbitrary =
      do first <- suchThat arbitrary isAsciiLower
         rest  <- suchThat arbitrary (and . (map isAsciiLower))
         return (ElementName (first:rest))

main = sample (arbitrary::Gen RepType)
\end{code}
\end{document}
