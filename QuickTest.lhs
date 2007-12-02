\documentclass{article}
%include polycode.fmt
\begin{document}

\section{Introduction}

\section{The Code}

\begin{code}
module QuickTest(
   main
   )  where

import Test.QuickCheck
import Text.PrettyPrint
import Control.Monad.State
import ConstrainedType
import Language.ASN1 hiding (NamedType, BitString)
import Data.Char
import Data.Maybe
import Data.Monoid
import Data.List hiding (groupBy)
import qualified Data.Set as S
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
import Data.Int

prettyConstraint :: (Ord a, Show a) => Constraint a -> Doc
prettyConstraint (Elem s) = text (show s)

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

prettyChoice :: Choice a -> Doc
prettyChoice NoChoice =
   empty
prettyChoice (ChoiceOption nt NoChoice) =
   prettyNamedType nt
prettyChoice (ChoiceOption nt xs) =
   vcat [prettyNamedType nt <> comma, prettyChoice xs]

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
                        return (RepType (SEQUENCE (Cons u v))),
         do x <- arbitrary
            case x of
               RepChoice u ->
                  return (RepType (CHOICE u))
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

\end{code}

Currently, we generate the invalid {\em NoChoice}, an illegal {\em CHOICE} of
no elements! A {\em CHOICE} has to have at least one element --- find the reference!!!

\begin{code}

data RepChoice = forall t . RepChoice (Choice t)

instance Arbitrary RepChoice where
   arbitrary =
      oneof [
         return (RepChoice NoChoice),
         do x  <- arbitrary
            xs <- arbitrary
            case x of
               RepNamedType u ->
                  case xs of
                     RepChoice us ->
                        return (RepChoice (ChoiceOption u us))
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

\end{code}

There's some duplicate code here and where CHOICE gets decoded.
Also check the encoding as there may be some duplicate there as well.

Two values of a CHOICE type are equal if their values are in the head
of the heterogeneous list or if the tails of the heterogeneous list are
equal.

\begin{code}

instance Eq (HL Nil (S Z)) where
   _ == _ = True

instance (Eq a, Eq (HL l (S Z))) => Eq (HL (a:*:l) (S Z)) where
   ValueC   _ _ == NoValueC _ _ = False
   NoValueC _ _ == ValueC _ _   = False
   NoValueC _ xs == NoValueC _ ys = xs == ys
   ValueC x _ == ValueC y _ = x == y
   
data RepChoiceVal = forall a . Eq (HL a (S Z))=> RepChoiceVal (Choice a) (HL a (S Z))

data RepNoChoiceVal = forall a . Eq (HL a (S Z)) => RepNoChoiceVal (Choice a) (HL a Z)

prettyChoiceVal :: Choice a -> (HL a (S Z)) -> Doc
prettyChoiceVal NoChoice _ = empty
prettyChoiceVal (ChoiceOption (NamedType n i t) cs) (NoValueC NoValue vs) =
   prettyChoiceVal cs vs
prettyChoiceVal (ChoiceOption (NamedType n i t) cs) (ValueC v vs) =
   prettyTypeVal t v

instance Show RepChoiceVal where
   show r =
      case r of
         RepChoiceVal t x ->
            render (prettyChoiceVal t x)

data Fum = forall a . Eq a => Fum (Choice a) (HL a Z)

data Fee = forall a . Eq a => Fee (Choice a) (HL a (S Z))

fum :: Choice a -> Gen Fum
fum (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- fum ts
      case u of
         RepTypeVal a v ->
            case us of
               Fum bs vs ->
                  return (Fum (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

arbitraryNoChoice :: Choice a -> Gen RepNoChoiceVal
arbitraryNoChoice NoChoice = 
   return (RepNoChoiceVal NoChoice EmptyHL)
arbitraryNoChoice (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitraryNoChoice ts
      case u of
         RepTypeVal a v ->
            case us of
               RepNoChoiceVal bs vs ->
                  return (RepNoChoiceVal (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

fee :: Choice a -> Gen Fee
fee (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- fee ts
      case u of
         RepTypeVal a v ->
            case us of
               Fee bs vs ->
                  return (Fee (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

arbitrary1stChoice :: Choice a -> Gen RepChoiceVal
arbitrary1stChoice (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitrary1stChoice ts
      case u of
         RepTypeVal a v ->
            case us of
               RepChoiceVal bs vs ->
                  return (RepChoiceVal (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

fuu :: Choice a -> Gen Fee
fuu (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- fum ts
      case u of
         RepTypeVal a v ->
            case us of
               Fum bs vs ->
                  return (Fee (ChoiceOption (NamedType n i a) bs) (ValueC v vs))

arbitrary1stChoice' :: Choice a -> Gen RepChoiceVal
arbitrary1stChoice' (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitraryNoChoice ts
      case u of
         RepTypeVal a v ->
            case us of
               RepNoChoiceVal bs vs ->
                  return (RepChoiceVal (ChoiceOption (NamedType n i a) bs) (ValueC v vs))

mun :: Int -> Choice a -> Gen Fee
mun 0 c =
   fuu c
mun 1 (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- fuu ts
      case u of
         RepTypeVal a v ->
            case us of
               Fee bs vs ->
                  return (Fee (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))
mun m (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- mun (m - 1) ts
      case u of
         RepTypeVal a v ->
            case us of
               Fee bs vs ->
                  return (Fee (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

arbitraryNthChoice :: Int -> Choice a -> Gen RepChoiceVal
arbitraryNthChoice 0 c =
   arbitrary1stChoice' c
arbitraryNthChoice m (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitraryNthChoice (m - 1) ts
      case u of
         RepTypeVal a v ->
            case us of
               RepChoiceVal bs vs ->
                  return (RepChoiceVal (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

arbitraryFee :: Choice a -> Gen Fee
arbitraryFee NoChoice =
   error "arbitraryChoice generating invalid length choice"   
arbitraryFee a =
   do n <- suchThat arbitrary (\n -> (n >= 0) && (n <= choiceLength a))
      mun n a

arbitraryChoice :: Choice a -> Gen RepChoiceVal
arbitraryChoice NoChoice =
   error "arbitraryChoice generating invalid length choice"   
arbitraryChoice a =
   do n <- suchThat arbitrary (\n -> (n >= 0) && (n <= ((choiceLength a) - 1)))
      arbitraryNthChoice n a

choiceLength :: Integral n => Choice a -> n
choiceLength NoChoice = 0
choiceLength (ChoiceOption _ ts) = 1 + (choiceLength ts)

-- bar :: Choice a -> Gen RepNoChoiceVal
bar x = return (foo x)   

foo x = RepNoChoiceVal x (noChoice x)

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
prettyTypeVal a@(BITSTRING []) x     = text (show x)
prettyTypeVal a@INTEGER x       = text (show x)
prettyTypeVal a@(RANGE t l u) x = prettyTypeVal t x
prettyTypeVal a@(SIZE t s e) x  = prettyTypeVal t x
prettyTypeVal a@(SEQUENCE s) x  = braces (prettySeqVal s x)
prettyTypeVal a@(CHOICE c) x = prettyChoiceVal c x

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
         do (BITSTRINGVal t x) <- arbitrary
            return (RepTypeVal t x),
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
arbitraryType (CHOICE c) =
   do r <- arbitraryChoice c
      case r of
         RepChoiceVal as vs ->
            return (RepTypeVal (CHOICE as) vs)

choice1 = 
   CHOICE xs 
      where
         xs = ChoiceOption (NamedType "a" Nothing INTEGER) NoChoice

seqChoices1 = 
   SEQUENCE elems
      where
         elems = Cons x (Cons y Nil)
         x = ETMandatory (NamedType "x" Nothing choice1)
         y = ETMandatory (NamedType "y" Nothing choice1)

choice2 = ChoiceOption (NamedType "z" Nothing INTEGER) (ChoiceOption (NamedType "a" Nothing seqChoices1) NoChoice)

\end{code}

Try this to generate arbitrary CHOICE: in this case a mixture of INTEGER and SEQUENCE.

\begin{code}

generateChoice = sample (arbitraryChoice choice2)

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

\end{code}

This really needs its own generator rather than using BitString.

\begin{code}

prop_2scomplement2 x =
   length (bitString x) `mod` 8 == 0 && (not (null (bitString x))) ==> 
      x == (BitString . to2sComplement . from2sComplement .bitString) x

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
             (Left e,_)   -> error ("Left " ++ e ++ ": Type = " ++ (render (prettyType t)) ++ " BitStream = " ++ show x)
             (Right xs,_) -> xs
      runTest t x y = runState (runErrorT (myMFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

main =
   do quickCheck prop_fromPerToPer
      quickCheck prop_WithinRange
      quickCheck prop_2scomplement1
      quickCheck prop_2scomplement2

\end{code}

\begin{code}

myMFromPer :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => ASNType a -> m a
myMFromPer t@INTEGER       = mmUntoPerInt t
myMFromPer r@(RANGE i l u) = mmUntoPerInt r
myMFromPer t@(BITSTRING []) = 
   (liftM (BitString . map fromIntegral) . fromPerBitString) t
myMFromPer t@(SIZE (BITSTRING _) _ _) = 
   (liftM (BitString . map fromIntegral) . fromPerBitString) t
myMFromPer (SEQUENCE s)    =
   do ps <- mmGetBits (l s)
      myMmFromPerSeq (map fromIntegral ps) s
   where
      l :: Integral n => Sequence a -> n
      l Nil = 0
      l (Cons (ETMandatory _) ts) = l ts
      l (Cons (ETOptional _ ) ts) = 1+(l ts)
myMFromPer t@(SIZE (SIZE _ _ _) _ _) = 
   let nt = multiSize t in myMFromPer nt
myMFromPer t = error ("This case is not handled in myMFromPer: " ++ render (prettyType t))

\end{code}

\begin{code}

myMmFromPerSeq :: (MonadState (B.ByteString,Int64) m, MonadError [Char] m) => BitStream -> Sequence a -> m a
myMmFromPerSeq _ Nil = return Empty
myMmFromPerSeq bitmap (Cons (ETMandatory (NamedType _ _ t)) ts) =
   do x <- myMFromPer t
      xs <- myMmFromPerSeq bitmap ts
      return (x:*:xs)
myMmFromPerSeq bitmap (Cons (ETOptional (NamedType _ _ t)) ts) =
   do if (head bitmap) == 0
         then
            do xs <- myMmFromPerSeq (tail bitmap) ts
               return (Nothing:*:xs)
         else
            do x <- myMFromPer t
               xs <- myMmFromPerSeq (tail bitmap) ts
               return ((Just x):*:xs)

\end{code}

\section{Testing BIT STRING}

\begin{code}

instance Arbitrary BitString where
   arbitrary =
      oneof [
         return (BitString []),
         liftM BitString (sized onesAndZeros)
         ]
      where
         onesAndZeros 0 = return []
         onesAndZeros n | n > 0 =
            do x <- oneof [return 0, return 1]
               xs <- subOnesAndZeros
               return (x:xs)
            where
               subOnesAndZeros = onesAndZeros (n `div` 2)

data OnlyBITSTRING = OnlyBITSTRING (ASNType BitString)

instance Arbitrary OnlyBITSTRING where
   arbitrary =
      oneof [
         return (OnlyBITSTRING (BITSTRING [])),
         sized onlyBITSTRING
         ]
      where
         onlyBITSTRING 0 = return (OnlyBITSTRING (BITSTRING []))
         onlyBITSTRING n | n > 0 =
            do (OnlyBITSTRING t) <- subOnlyBITSTRING
               let Constrained lb ub = sizeLimit t
               nl <- suchThat (suchThat arbitrary (f2 lb ub)) (>= 0)
               nu <- suchThat (suchThat arbitrary (f2 lb ub)) (>= nl)
               return (OnlyBITSTRING (SIZE t (Elem (S.fromList [nl..nu])) NoMarker))
            where
               subOnlyBITSTRING = onlyBITSTRING (n `div` 2)

instance Show OnlyBITSTRING where
   show r =
      case r of
         OnlyBITSTRING n ->
            render (prettyType n)

arbitraryBITSTRING :: OnlyBITSTRING -> Gen BitString
arbitraryBITSTRING x =
   case x of
      OnlyBITSTRING y ->
         case y of
            (BITSTRING []) ->
               arbitrary
            SIZE t s _ ->
               if S.null (evalCons s)
                  then
                     error "arbitraryBITSTRING: generating impossible constraints"
                  else
                     g s
   where
      h 0 = return []
      h n =
         do x <- oneof [return 0, return 1]
            xs <- h (n - 1)
            return (x:xs)
      f = (liftM BitString) . h
      g (Elem ns) = oneof (map f (S.toList ns))

data BITSTRINGVal = BITSTRINGVal (ASNType BitString) BitString

instance Show BITSTRINGVal where
   show (BITSTRINGVal t x) =
      show (prettyType t) ++ ": " ++ show x

instance Arbitrary BITSTRINGVal where
   arbitrary =
      do r <- arbitrary
         x <- arbitraryBITSTRING r
         case r of
            OnlyBITSTRING t ->
               return (BITSTRINGVal t x)

\end{code}

\begin{code}

t3 = NamedType "T3" Nothing (SEQUENCE (
        Cons (ETMandatory (NamedType "first" Nothing INTEGER)) (
           Cons (ETMandatory (NamedType "second" Nothing INTEGER)) Nil)))

\end{code}

\end{document}
