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
   prettyType
   )  where

import Test.QuickCheck
import Text.PrettyPrint
import Control.Monad.State
import ConstrainedType
import Language.ASN1 hiding (NamedType)
import Data.Char
import Data.Maybe
import Data.Monoid
import Data.List hiding (groupBy)
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
-- import Test.QuickCheck.Gen

prettyType :: ASNType a -> Doc
prettyType INTEGER =
   text "INTEGER"
prettyType(RANGE x l u) =
   prettyType x <+> outer x l u
prettyType (SEQUENCE x) =
   text "SEQUENCE" <> space <> braces (prettySeq x)

outer :: ASNType a -> Maybe a -> Maybe a -> Doc
outer INTEGER Nothing  Nothing  = parens (text "MIN"    <> text ".." <> text "MAX")
outer INTEGER Nothing (Just y)  = parens (text "MIN"    <> text ".." <> text (show y))
outer INTEGER (Just x) Nothing  = parens (text (show x) <> text ".." <> text "MAX")
outer INTEGER (Just x) (Just y) = parens (text (show x) <> text ".." <> text (show y))
outer (RANGE t l u) x y = outer t x y
\end{code}

\begin{code}
prettySeq :: Sequence a -> Doc
prettySeq Nil =
   empty
prettySeq (Cons x Nil) =
   prettyElem x
prettySeq (Cons x xs) =
   vcat [prettyElem x <> comma, prettySeq xs]

prettyElem :: ElementType a -> Doc
prettyElem (ETMandatory nt) = prettyNamedType nt

prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n _ ct) =
   text n <+> prettyType ct

data RepType = forall t . RepType (ASNType t)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         do r <- arbitrary
            let (OnlyINTEGER t) = r
            return (RepType t),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u ->
                  case y of
                     RepSeq v ->
                        return (RepType (SEQUENCE (Cons u v)))
         ]

instance Show RepType where
   show x =
      case x of
         RepType y ->
            render (prettyType y)

data RepElementType = forall t . RepElementType (ElementType t)

instance Arbitrary RepElementType where
   arbitrary =
      do rnt <- arbitrary
         case rnt of
            RepNamedType nt ->
               return (RepElementType (ETMandatory nt))

data RepNamedType = forall t . RepNamedType (NamedType t)

instance Arbitrary RepNamedType where
   arbitrary =
      do name <- arbitrary
         rct   <- arbitrary
         case rct of
            RepType ct ->
               return (RepNamedType (NamedType (elementName name) Nothing ct))

newtype ElementName = ElementName {elementName :: String}
   deriving Show

instance Arbitrary ElementName where
   arbitrary =
      do first <- suchThat arbitrary isAsciiLower
         rest  <- suchThat arbitrary (and . (map isAsciiLower))
         return (ElementName (first:rest))

data RepSeq = forall t . RepSeq (Sequence t)

instance Arbitrary RepSeq where
   arbitrary =
      oneof [
         return (RepSeq Nil),
         do x  <- arbitrary
            xs <- arbitrary
            case x of
               RepElementType u ->
                  case xs of
                     RepSeq us ->
                        return (RepSeq (Cons u us))
         ]


range :: ASNType Integer -> Maybe (Maybe Integer,Maybe Integer)
range INTEGER = return (Nothing,Nothing)
range (RANGE t l u) =
   do (m,v) <- range t
      h1 (f1 l m) (g1 u v)

f1 Nothing  Nothing = Nothing
f1 Nothing  (Just y) = Just y
f1 (Just x) Nothing  = Just x
f1 (Just x) (Just y) = Just (max x y)
g1 Nothing  Nothing  = Nothing
g1 Nothing  (Just y) = Just y
g1 (Just x) Nothing  = Just x
g1 (Just x) (Just y) = Just (min x y)
h1 Nothing  Nothing  = Just (Nothing,Nothing)
h1 Nothing  (Just y) = Just (Nothing,Just y)
h1 (Just x) Nothing  = Just (Just x, Nothing)
h1 (Just x) (Just y)
   | x > y = Nothing
   | otherwise = Just (Just x,Just y)


data OnlyINTEGER = OnlyINTEGER (ASNType Integer)

instance Arbitrary OnlyINTEGER where
   arbitrary =
      oneof [
         return (OnlyINTEGER INTEGER),
         sized onlyINTEGER
         ]
      where
         onlyINTEGER 0 = return (OnlyINTEGER INTEGER)
         onlyINTEGER n | n > 0 =
            do l <- arbitrary
               u <- suchThat arbitrary (fromMaybe True . (g l))
               t <- subOnlyINTEGER
               return (f t l u)
            where
               subOnlyINTEGER = onlyINTEGER (n `div` 2)
         f (OnlyINTEGER x) l u = OnlyINTEGER (RANGE x l u)
         g l u =
            do m <- l
               n <- u
               return (n >= m)

instance Show OnlyINTEGER where
   show r =
      case r of
         OnlyINTEGER n ->
            render (prettyType n)

arbitraryINTEGER :: OnlyINTEGER -> Gen (Maybe Integer)
arbitraryINTEGER x =
   case x of
      OnlyINTEGER y ->
         case y of
            INTEGER ->
               do n <- arbitrary
                  return (Just n)
            RANGE t l u ->
               do let r = range y
                  case r of
                     Nothing ->
                        return Nothing
                     Just (x,y) ->
                        suchThat (arbitraryINTEGER (OnlyINTEGER t)) (g x y)
   where
      f :: Maybe Integer -> Maybe Integer -> Integer -> Bool
      f Nothing Nothing   _ = True
      f Nothing (Just u)  x = x <= u
      f (Just l) Nothing  x = x >= l
      f (Just l) (Just u) x = (x >= l) && (x <= u)
      g _ _ Nothing  = False
      g x y (Just z) = f x y z

instance Eq Nil where
  _ == _ = True

instance (Eq a, Eq b) => Eq (a:*:b) where
   x:*:xs == y:*:ys =
      x == y && xs == ys

data RepSeqVal = forall a . Eq a => RepSeqVal (Sequence a) a

prettySeqVal :: Sequence a -> a -> Doc
prettySeqVal Nil _ = empty
prettySeqVal (Cons e Nil) (x:*:Empty) =
   prettyElementTypeVal e x
prettySeqVal (Cons e l) (x:*:xs) =
   prettyElementTypeVal e x <> comma $$ prettySeqVal l xs

instance Show RepSeqVal where
   show r =
      case r of
         RepSeqVal t x ->
            render (prettySeqVal t x)

prettyElementTypeVal :: ElementType a -> a -> Doc
prettyElementTypeVal (ETMandatory (NamedType n _ t)) x =
   text n <+> prettyTypeVal t x

arbitrarySeq :: Sequence a -> Gen RepSeqVal
arbitrarySeq Nil =
   return (RepSeqVal Nil Empty)
arbitrarySeq (Cons (ETMandatory (NamedType n i t)) ts) =
   do u <- arbitraryType t
      us <- arbitrarySeq ts
      case u of
         RepTypeVal a v ->
            case us of
               RepSeqVal bs vs ->
                  return (RepSeqVal (Cons (ETMandatory (NamedType n i a)) bs) (v:*:vs))

instance Arbitrary RepSeqVal where
   arbitrary =
      oneof [
         return (RepSeqVal Nil Empty),
         do u <- arbitrary
            case u of
               RepTypeVal s x ->
                  do us <- arbitrary
                     case us of
                        RepSeqVal t xs ->
                           do e <- arbitrary
                              return (RepSeqVal (Cons (ETMandatory (NamedType (elementName e) Nothing s)) t) (x:*:xs))
         ]

data RepTypeVal = forall a . Eq a => RepTypeVal (ASNType a) a

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal a@INTEGER x       = text (show x)
prettyTypeVal a@(RANGE t l u) x = prettyTypeVal t x
prettyTypeVal a@(SEQUENCE s) x  = braces (prettySeqVal s x)

{-
instance Eq RepTypeVal where
   r == s =
      case r of
         RepTypeVal t x ->
            case s of
               RepTypeVal u y ->
                  True
-}

instance Show RepTypeVal where
   show r =
      case r of
         RepTypeVal t x ->
            render (prettyType t <> colon <+> prettyTypeVal t x)

instance Arbitrary RepTypeVal where
   arbitrary =
      oneof [
         do (INTEGERVal t mn) <- arbitrary
            case mn of
               Nothing ->
                  return (RepTypeVal t (-17))
               Just n ->
                  return (RepTypeVal t n),
            do r <- arbitrary
               case r of
                  RepSeqVal s xs ->
                     return (RepTypeVal (SEQUENCE s) xs)
         ]

arbitraryType :: ASNType a -> Gen RepTypeVal
arbitraryType INTEGER =
   do n <- arbitrary
      return (RepTypeVal INTEGER n)
arbitraryType (RANGE x l u) =
   do y <- arbitraryType x
      case y of
         RepTypeVal INTEGER n ->
            undefined
   where
      g l u =
         do m <- l
            n <- u
            return (n >= m)
arbitraryType (SEQUENCE s) =
   do r <- arbitrarySeq s
      case r of
         RepSeqVal as vs ->
            return (RepTypeVal (SEQUENCE as) vs)

data INTEGERVal = INTEGERVal (ASNType Integer) (Maybe Integer)

instance Show INTEGERVal where
   show (INTEGERVal t x) =
      show (prettyType t) ++ ": " ++ show x

instance Arbitrary INTEGERVal where
   arbitrary =
      do r <- arbitrary
         x <- arbitraryINTEGER r
         case r of
            OnlyINTEGER t ->
               return (INTEGERVal t x)

f2 :: Maybe Integer -> Maybe Integer -> Integer -> Bool
f2 Nothing Nothing   _ = True
f2 Nothing (Just u)  x = x <= u
f2 (Just l) Nothing  x = x >= l
f2 (Just l) (Just u) x = (x >= l) && (x <= u)
\end{code}

The generated Integer should be within the lower and upper bound of the constraints.

\begin{code}
prop_WithinRange (INTEGERVal t Nothing) =
   case range t of
      Nothing ->
         True
      Just (x,y) ->
         False
prop_WithinRange (INTEGERVal t (Just n)) =
   case range t of
      Nothing ->
         False
      Just (x,y) ->
         f2 x y n


prop_2scomplement1 x =
   x == from2sComplement (to2sComplement x)

prop_2scomplement2 x =
   x == to2sComplement (from2sComplement x)

valid :: ASNType a -> a -> Bool
valid r@(RANGE t l u) n
    = case range r of
        Nothing -> False
        Just (x,y) ->
         f2 x y n
valid (SEQUENCE (Cons (ETMandatory (NamedType n t a)) as)) (x:*:xs)
    = valid a x && valid (SEQUENCE as) xs
valid (SEQUENCE (Cons (ETExtMand (NamedType n t a)) as)) (Just x:*:xs)
    = valid a x && valid (SEQUENCE as) xs
valid (SEQUENCE (Cons (ETDefault (NamedType n t a) v) as)) (Just x:*:xs)
    = valid a x && valid (SEQUENCE as) xs
valid (SEQUENCE (Extens as)) xs
    = valid (SEQUENCE as) xs
valid _ _ = True

prop_fromPerToPer x =
   case x of
      RepTypeVal t y ->
        if valid t y
          then y == runFromPer t (toPer8s t y)
           else True
   where
      runFromPer :: ASNType a -> BitStream -> a
      runFromPer t x =
        case runTest t x 0 of
             (Left _,_)   -> undefined
             (Right xs,_) -> xs
      runTest t x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

main =
   do quickCheck prop_fromPerToPer
      quickCheck prop_WithinRange
      quickCheck prop_2scomplement1
      quickCheck prop_2scomplement2

\end{code}

\end{document}
