\documentclass{article}
%include polycode.fmt
\begin{document}

\section{Introduction}

\section{The Code}

\begin{code}
module QuickTest(
   main,
   genModule,
   genModule',
   genModule'',
   RepTypeVal(..)
   )  where

import Test.QuickCheck
import Text.PrettyPrint
import Control.Monad.State
import ConstrainedType
import Pretty
import Language.ASN1 hiding (NamedType, BitString, ComponentType)
import Data.Char
import Data.Maybe
import Data.Monoid
import Data.List hiding (groupBy)
import qualified Data.Set as S
import Control.Monad.Error
import qualified Data.ByteString.Lazy as B
import Data.Int
import Relabel
import qualified Rename as R
import Data.Traversable
import Control.Arrow hiding ((<+>))

\end{code}

\begin{code}

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

data RepElementType = forall t . RepElementType (ComponentType t)

instance Arbitrary RepElementType where
   arbitrary =
      do rnt <- arbitrary
         case rnt of
            RepNamedType nt ->
               return (RepElementType (CTMandatory nt))

data RepNamedType = forall t . RepNamedType (NamedType t)

instance Arbitrary RepNamedType where
   arbitrary =
      do name <- arbitrary
         rct   <- arbitrary
         tv <- arbitrary
         case rct of
            RepType ct ->
               do let f :: ASNType a -> TagPlicity
                      f (CHOICE _) = Explicit
                      f _          = Implicit
                  return (RepNamedType (NamedType (elementName name) (Just (Context, tv, (f ct))) ct))

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

Now we can generate {\em CHOICE} where the last element is always some form of {\em INTEGER}.

\begin{code}

data RepChoice = forall t . RepChoice (Choice t)

instance Arbitrary RepChoice where
   arbitrary =
      oneof [
         do name <- arbitrary
            r    <- arbitrary
            let (OnlyINTEGER t) = r
            return (RepChoice (ChoiceOption (NamedType (elementName name) Nothing t) NoChoice)),
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

\end{code}

A word of explanation. This will do for now but arbitrary {\em Integer}s aren't very arbitrary;
in fact, they are rather small. Furthermore, we now never generate {\em MIN} or {\em MAX}.

\begin{code}

data OnlyINTEGER = OnlyINTEGER (ASNType Integer)

instance Arbitrary OnlyINTEGER where
   arbitrary =
      oneof [
         return (OnlyINTEGER INTEGER) -- ,
--          sized onlyINTEGER
         ]
      where
         onlyINTEGER 0 = return (OnlyINTEGER INTEGER)
         onlyINTEGER n | n > 0 =
            do t <- subOnlyINTEGER
               case t of
                  OnlyINTEGER s ->
                     do let (l,u) = fromJust (range s)
                        l' <- suchThat arbitrary (f2 l u)
                        u' <- suchThat arbitrary (f2 (Just l') u)
                        return (f t (Just l') (Just u'))
            where
               subOnlyINTEGER = onlyINTEGER (n `div` 2)
         f (OnlyINTEGER x) l u = OnlyINTEGER (RANGE x l u)

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

data RepSeqVal = forall a . Eq a => RepSeqVal (Sequence a) a

instance Show RepSeqVal where
   show r =
      case r of
         RepSeqVal t x ->
            render (prettyVal t x)

arbitrarySeq :: Sequence a -> Gen RepSeqVal
arbitrarySeq Nil =
   return (RepSeqVal Nil Empty)
arbitrarySeq (Cons (CTMandatory (NamedType n i t)) ts) =
   do u <- arbitraryType t
      us <- arbitrarySeq ts
      case u of
         RepTypeVal a v ->
            case us of
               RepSeqVal bs vs ->
                  return (RepSeqVal (Cons (CTMandatory (NamedType n i a)) bs) (v:*:vs))

\end{code}

There's some duplicate code here and where CHOICE gets decoded.
Also check the encoding as there may be some duplicate there as well.

Two values of a CHOICE type are equal if their values are in the head
of the heterogeneous list or if the tails of the heterogeneous list are
equal.

\begin{code}

data RepChoiceVal = forall a . Eq (HL a (S Z))=> RepChoiceVal (Choice a) (HL a (S Z))

data RepNoChoiceVal = forall a . Eq (HL a (S Z)) => RepNoChoiceVal (Choice a) (HL a Z)

instance Show RepChoiceVal where
   show r =
      case r of
         RepChoiceVal t x ->
            render (prettyVal t x)

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

arbitrary1stChoice :: Choice a -> Gen RepChoiceVal
arbitrary1stChoice (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitrary1stChoice ts
      case u of
         RepTypeVal a v ->
            case us of
               RepChoiceVal bs vs ->
                  return (RepChoiceVal (ChoiceOption (NamedType n i a) bs) (NoValueC NoValue vs))

arbitrary1stChoice' :: Choice a -> Gen RepChoiceVal
arbitrary1stChoice' (ChoiceOption (NamedType n i t) ts) =
   do u <- arbitraryType t
      us <- arbitraryNoChoice ts
      case u of
         RepTypeVal a v ->
            case us of
               RepNoChoiceVal bs vs ->
                  return (RepChoiceVal (ChoiceOption (NamedType n i a) bs) (ValueC v vs))

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

arbitraryChoice :: Choice a -> Gen RepChoiceVal
arbitraryChoice NoChoice =
   error "arbitraryChoice generating invalid length choice"
arbitraryChoice a =
   do n <- suchThat arbitrary (\n -> (n >= 0) && (n <= ((choiceLength a) - 1)))
      arbitraryNthChoice n a

choiceLength :: Integral n => Choice a -> n
choiceLength NoChoice = 0
choiceLength (ChoiceOption _ ts) = 1 + (choiceLength ts)

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
                              return (RepSeqVal (Cons (CTMandatory (NamedType (elementName e) Nothing s)) t) (x:*:xs))
         ]

data RepTypeVal = forall a . Eq a => RepTypeVal (ASNType a) a

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
                     return (RepTypeVal (SEQUENCE s) xs),
            do r <- arbitrary
               case r of
                  RepChoice c ->
                     do a <- arbitraryChoice c
                        case a of
                           RepChoiceVal t v ->
                              return (RepTypeVal (CHOICE t) v)
         ]

arbitraryType :: ASNType a -> Gen RepTypeVal
arbitraryType INTEGER =
   do n <- arbitrary
      return (RepTypeVal INTEGER n)
arbitraryType t@(RANGE x l u) =
   do y <- arbitraryINTEGER (OnlyINTEGER t)
      return (RepTypeVal t (fromJust y))
{-
   do y <- arbitraryType x
      case y of
         RepTypeVal INTEGER n ->
            error "Foo" -- undefined
-}
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

\end{code}

\section{INTEGER}

The generated INTEGER type should be valid?

\begin{code}

prop_validINTEGER t =
   case t of
      OnlyINTEGER u ->
         isJust (range u)

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

prop_fromPerToPer x =
   case x of
      RepTypeVal t y ->
         let t' = legalise t in
            y == runFromPer t' (toPer8s t' y)
   where
      runFromPer :: ASNType a -> BitStream -> a
      runFromPer t x =
        case runTest t x 0 of
             (Left e,_)   -> error ("Left " ++ e ++ ": Type = " ++ (render (prettyType t)) ++ " BitStream = " ++ show x)
             (Right xs,_) -> xs
      runTest t x y = runState (runErrorT (mFromPer t)) (B.pack (map (fromIntegral . fromNonNeg) (groupBy 8 x)),y)

main =
   do quickCheck prop_fromPerToPer
      quickCheck prop_validINTEGER
      quickCheck prop_WithinRange
      quickCheck prop_2scomplement1
--       quickCheck prop_2scomplement2

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
               return (OnlyBITSTRING (SIZE t (Elem (nl,nu)) NoMarker))
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
               if null (evalCons s)
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
      g (Elem ns) = do n <- choose ns
                       f n

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

\section{Tags}

\begin{code}

instance Show RepChoice where
   show x =
      case x of
         RepChoice y ->
            render (pretty y)

legalise :: ASNType a -> ASNType a
legalise = unShadow . relabel . shadow

legalName :: ASNType a -> ASNType a
legalName = R.unShadow . R.rename . R.shadow

repsRelabel us =
   p'
   where
      g r =
         case r of
            RepType t ->
               do x <- Data.Traversable.mapM (\_ -> update) (shadow t)
                  return (RepType (unShadow x))
      h rs = Control.Monad.State.sequence (map g rs)
      f rs = runState (h rs) 0
      (p',q') = f us

repTypeValsRelabel us =
   p'
   where
      g r =
         case r of
            RepTypeVal t y ->
               do x <- Data.Traversable.mapM (\_ -> update) (shadow t)
                  return (RepTypeVal (unShadow x) y)
      h rs = Control.Monad.State.sequence (map g rs)
      f rs = runState (h rs) 0
      (p',q') = f us

repsRename us =
   p'
   where
      g r =
         case r of
            RepType t ->
               do x <- Data.Traversable.mapM (\_ -> R.update) (R.shadow t)
                  return (RepType (R.unShadow x))
      h rs = Control.Monad.State.sequence (map g rs)
      f rs = runState (h rs) 0
      (p',q') = f us

repTypeValsRename us =
   p'
   where
      g r =
         case r of
            RepTypeVal t y ->
               do x <- Data.Traversable.mapM (\_ -> R.update) (R.shadow t)
                  return (RepTypeVal (R.unShadow x) y)
      h rs = Control.Monad.State.sequence (map g rs)
      f rs = runState (h rs) 0
      (p',q') = f us

typeAssify :: [RepTypeVal] -> [RepTypeVal]
typeAssify xs =
   zipWith ($) (map (g $) [1..]) xs
   where
      g n r = 
         case r of
            RepTypeVal t y ->
               RepTypeVal (TYPEASS ("Type" ++ (show n)) Nothing t) y

prettyRepType r =
   case r of
      RepType t ->
         prettyType t

prettyRepTypeVal r =
   case r of
      RepTypeVal t x ->
         (prettyType t, prettyTypeVal t x)

genModule =
 do xs <- sample' (arbitrary :: Gen RepType)
    return (prettyModule xs)

genModule' = sample' (arbitrary :: Gen RepTypeVal)

genModule'' =
   do xs <- genModule'
      return (typeAssify xs)

prettyModuleBody xs =
 vcat (zipWith (<+>) typeNames (map prettyRepType . repsRename . repsRelabel $ xs))
 where
   typeNames = map ((<+> text "::=") . (text "Type" <>) . text. show) [1..]

prettyModuleValsBody xs =
   vcat (map (uncurry ($$)) (prefixPairs (map valueTypeName prefixes) tsvs))
   where
      tsvs = map prettyRepTypeVal . repTypeValsRename . repTypeValsRelabel $ xs
      typeNames = (text "Type" <>) . text
      valueNames = (text "value" <>) . text
      prefixes = map ((typeNames &&& valueNames) . show) [1..]
      valueTypeName (t,v) = (t <+> text "::=", v <+> t <+> text "::=")
      prefixPairs ps xs = zipWith (\(p1,p2) (t,v) -> ((p1 <+> t), (p2 <+> v))) ps xs

prettyModuleWithVals xs =
   text "FooBar {1 2 3 4 5 6} DEFINITIONS ::="
   $$
   nest 2 (text "BEGIN")
   $$
   nest 4 (prettyModuleValsBody xs)
   $$
   nest 2 (text "END")

prettyModule xs =
   text "FooBar {1 2 3 4 5 6} DEFINITIONS ::="
   $$
   nest 2 (text "BEGIN")
   $$
   nest 4 (prettyModuleBody xs)
   $$
   nest 2 (text "END")

\end{code}

\end{document}
