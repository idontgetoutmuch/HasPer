{-# OPTIONS_GHC -XFlexibleInstances -XGADTs -XMultiParamTypeClasses -XFlexibleContexts  #-}

module LatticeMod where

import Data.Char
import Data.List
import Control.Monad.Error
import RestrictedCharacterStrings

class IC a where
    makeIC :: InfInteger -> InfInteger -> a
    getLower :: a -> InfInteger
    getUpper :: a -> InfInteger
    within :: a -> a -> Bool
    serialCombine :: a -> a -> a
    exceptIC :: a -> a -> a


class RS a where
    getString :: a -> String
    makeString :: String -> a
    exceptRS :: a -> a -> a
    exceptRS = exceptPAC


class Lattice a where
   bottom, top :: a
   meet, ljoin  :: a -> a -> a


class Lattice a => BooleanAlgebra a where
    complement :: a -> a

data IntegerConstraint = IntegerConstraint {lower :: InfInteger, upper :: InfInteger}
   deriving (Show, Eq)

-- ValidIntegerConstraint is used for the validity testing of a value against a constraint. Thus, unlike an
-- effective constraint (which is used to produce encoding in a small number of bits) and is always a contiguous
-- set of values, this type represents the true result of set combinations of constraints which may be non-contiguous.

data ValidIntegerConstraint = Valid [IntegerConstraint]
    deriving (Show, Eq)


instance IC IntegerConstraint where
    makeIC l u = IntegerConstraint l u
    getLower (IntegerConstraint l u) = l
    getUpper (IntegerConstraint l u) = u
    within a b
     =  let la = getLower a
            lb = getLower b
            ua = getUpper a
            ub = getUpper b
        in
            b == top
            || lb == NegInf && ub <= ua && ub >= la
            || ub == PosInf && lb >= la && lb <= ua
            || lb >= la && ub <= ua
    serialCombine a@(IntegerConstraint l1 u1) b@(IntegerConstraint l2 u2)
        | b == bottom = bottom
        | b == top    = a
        | l2 == NegInf && u2 <= u1
                      = IntegerConstraint l1 u2
        | u2 == PosInf && l2 >= l1
                      = IntegerConstraint l2 u1
        | otherwise = b
    exceptIC = exceptIntCon


instance IC ValidIntegerConstraint where
    makeIC l u = Valid [makeIC l u]
    getLower (Valid ls) = (getLower . head) ls
    getUpper (Valid ls) = (getUpper . last) ls
    within (Valid ls) (Valid []) = True
    within (Valid ls) (Valid (f:r))
        = or (map (flip within f) ls) && within (Valid ls) (Valid r)
    serialCombine (Valid ls) (Valid xs)
        = Valid (map (updateVIC ls) xs)
          where
            updateVIC (x:y) f
                | within x f = serialCombine x f
                | otherwise = updateVIC y f
    exceptIC = exceptVIC


instance Bounded InfInteger where
   minBound = NegInf
   maxBound = PosInf

data InfInteger = NegInf | V Integer | PosInf
    deriving (Show, Ord, Eq)

instance Num InfInteger where
   PosInf + _ = PosInf
   _ + PosInf = PosInf
   NegInf + _ = NegInf
   _ + NegInf = NegInf
   (V x) + (V y) = V (x + y)
   PosInf - _ = PosInf
   _ - PosInf = NegInf
   NegInf - _ = NegInf
   _ - NegInf = PosInf
   (V x) - (V y) = V (x - y)
   fromInteger v = V v


-- Note that this instantiation generates effective
-- constraint-based meet and join. For example,
-- (1..3) `ljoin` (5..8) is (1..8).

instance Lattice IntegerConstraint where
   bottom = IntegerConstraint PosInf NegInf
   top = IntegerConstraint NegInf PosInf
   (IntegerConstraint l1 u1) `ljoin` {-`meet`-} (IntegerConstraint l2 u2)
        = IntegerConstraint (min l1 l2) (max u1 u2)
   (IntegerConstraint l1 u1) `meet` {-`ljoin`-} (IntegerConstraint l2 u2)
      | u2 < l1   = bottom
      | l2 > u1   = bottom
      | otherwise = IntegerConstraint (max l1 l2) (min u1 u2)

instance Lattice ValidIntegerConstraint where
   bottom = Valid [bottom]
   top = Valid [top]
   Valid ic1 `ljoin` Valid ic2
        = Valid (listUnion ic1 ic2)
   Valid a `meet` Valid b
      = Valid (listInter a b)

unionIC a@(IntegerConstraint l1 u1) b@(IntegerConstraint l2 u2)
    | l2 > u1+1  = a:[b]
    | l1 > u2+1  = b:[a]
      | otherwise = [IntegerConstraint (min l1 l2) (max u1 u2)]

listUnion [a] [b] = unionIC a b
listUnion (f:r) (s:t)
    | getUpper f < getLower s - 1
        = f: listUnion r (s:t)
    | getUpper s < getLower f
        = s : listUnion (f:r) t
    | otherwise
        = let g = unionIC f s
              h = listUnion g r
          in
            listUnion h t
listUnion ls [] = ls
listUnion [] ls = ls

listInter (f:r) b
      = let a = map (f `meet`) b
            c = filter (/= bottom) a
            x = listInter r  b
        in
         c++x
listInter ls [] = []
listInter [] ls = []


ic1 = IntegerConstraint 1 3
ic2 = IntegerConstraint 7 11
ic3 = IntegerConstraint 4 8
ic4 = IntegerConstraint 15 17
ic5 = IntegerConstraint 14 21
ic6 = IntegerConstraint 19 25




instance BooleanAlgebra ValidIntegerConstraint where
    complement a@(Valid x)
        | a == bottom = top
        | a == top = bottom
        | otherwise = Valid (notVIC x)

notVIC [c]
    | getLower c == NegInf = [IntegerConstraint (getUpper c + 1) PosInf]
    | getUpper c == PosInf = [IntegerConstraint NegInf (getLower c - 1)]
    | otherwise = [IntegerConstraint NegInf (getLower c - 1), IntegerConstraint (getUpper c + 1) PosInf]
notVIC (f:g:r)
    | getLower f == NegInf = IntegerConstraint (getUpper f + 1) (getLower g - 1): notVIC' (g:r)
      | otherwise = IntegerConstraint NegInf (getLower f - 1) : notVIC' (f:g:r)

notVIC' [f]
    | getUpper f == PosInf = []
    | otherwise = [IntegerConstraint (getUpper f + 1) PosInf]
notVIC' (f:g:r) = IntegerConstraint (getUpper f + 1) (getLower g - 1) : notVIC' (g:r)



lowerHalf x = IntegerConstraint NegInf (V x)
upperHalf x = IntegerConstraint (V x) PosInf


exceptIntCon a@(IntegerConstraint l1 u1) (IntegerConstraint l2 u2)
    | l1 < l2 && u1 > u2 = a
    | l1 < l2 = IntegerConstraint l1 (l2-1)
    | u1 > u2 = IntegerConstraint (u2+1) u1
    | otherwise = bottom


-- except for a ValidIntegerConstraint can be defined by using the
-- equivalence  x except y = x /\ (not y)
exceptVIC a b = a `meet` (complement b)

-- Can use \\ here since no repetition in permitted string
exceptPAC :: RS a => a -> a -> a
exceptPAC a b
    = let s1 = getString a
          s2 = getString b
      in makeString (s1 \\ s2)

instance Lattice a => Lattice (Either String a) where
   bottom = Right bottom
   top    = Right top
   (Left s)  `meet` _          = Left s
   _         `meet` (Left s)   = Left s
   (Right x) `meet` (Right y)  = Right (x `meet` y)
   (Left s)  `ljoin` _         = Left s
   _         `ljoin` (Left s)  = Left s
   (Right x) `ljoin` (Right y) = Right (x `ljoin` y)

instance BooleanAlgebra a => BooleanAlgebra (Either String a) where
    complement (Left s) = Left s
    complement (Right x) = Right (complement x)


instance Lattice VisibleString where
    bottom = VisibleString ""
    top = VisibleString (" " ++ ['!'..'~'])
    (VisibleString s1) `meet` (VisibleString s2) = VisibleString (interString s1 s2)
    (VisibleString s1) `ljoin` (VisibleString s2) = VisibleString (unionString s1 s2)

instance Lattice PrintableString where
    bottom = PrintableString ""
    top = PrintableString (" '()+,-./:=?" ++ ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'])
    (PrintableString s1) `meet` (PrintableString s2) = PrintableString (interString s1 s2)
    (PrintableString s1) `ljoin` (PrintableString s2) = PrintableString (unionString s1 s2)


instance Lattice NumericString where
    bottom = NumericString ""
    top = NumericString (" " ++ ['0'..'9'])
    (NumericString s1) `meet` (NumericString s2) = NumericString (interString s1 s2)
    (NumericString s1) `ljoin` (NumericString s2) = NumericString (unionString s1 s2)

instance Lattice IA5String where
    bottom = IA5String ""
    top = IA5String (['\NUL'..'\US'] ++ ['!'..'~'])
    (IA5String s1) `meet` (IA5String s2) = IA5String (interString s1 s2)
    (IA5String s1) `ljoin` (IA5String s2) = IA5String (unionString s1 s2)

instance Lattice UniversalString where
    bottom = UniversalString ""
    top = UniversalString ([minBound..maxBound])
    (UniversalString s1) `meet` (UniversalString s2) = UniversalString (interString s1 s2)
    (UniversalString s1) `ljoin` (UniversalString s2) = UniversalString (unionString s1 s2)


instance Lattice BMPString where
    bottom = BMPString ""
    top = BMPString ([minBound..(chr (2^16-1))])
    (BMPString s1) `meet` (BMPString s2) = BMPString (interString s1 s2)
    (BMPString s1) `ljoin` (BMPString s2) = BMPString (unionString s1 s2)

unionString [] s = s
unionString (f:r) s = if elem f s
            then unionString r s
            else f : unionString r s

interString [] s = []
interString (f:r) s = if elem f s
            then f : interString r s
            else interString r s



instance RS VisibleString where
    getString (VisibleString s) = s
    makeString s = VisibleString s


instance RS PrintableString where
    getString (PrintableString s) = s
    makeString s = PrintableString s

instance RS NumericString where
    getString (NumericString s) = s
    makeString s = NumericString s

instance RS IA5String where
    getString (IA5String s) = s
    makeString s = IA5String s

instance RS UniversalString where
    getString (UniversalString s) = s
    makeString s = UniversalString s

instance RS BMPString where
    getString (BMPString s) = s
    makeString s = BMPString s

data ResStringConstraint i a = ResStringConstraint i a
    deriving (Show,Eq)
data ExtResStringConstraint i a
    = ExtResStringConstraint (ResStringConstraint i a) (ResStringConstraint i a) Bool
    deriving (Show,Eq)

extensible :: (ExtResStringConstraint i a) -> Bool
extensible (ExtResStringConstraint _ _ b) = b

getRC :: (ExtResStringConstraint i a) -> ResStringConstraint i a
getRC (ExtResStringConstraint r _ _) = r

getEC :: (ExtResStringConstraint i a) -> ResStringConstraint i a
getEC (ExtResStringConstraint _ e _) = e

getSC :: ResStringConstraint i a -> i
getSC (ResStringConstraint i s) = i

getPAC :: RS a => ResStringConstraint i a -> a
getPAC (ResStringConstraint i s) = s

instance (Lattice a, Lattice i,RS a, Eq a, Eq i, IC i) => Lattice (ResStringConstraint i a) where
    bottom = ResStringConstraint bottom bottom
    top = ResStringConstraint top top
    (ResStringConstraint i1 s1) `ljoin` (ResStringConstraint i2 s2)
        = if (s1 == bottom && i2 == bottom) || (i1 == bottom && s2 == bottom)
               then top
               else ResStringConstraint (i1 `ljoin` i2) (s1 `ljoin` s2)
    (ResStringConstraint i1 s1) `meet` (ResStringConstraint i2 s2)
        = ResStringConstraint (i1 `meet` i2) (s1 `meet` s2)


instance (Lattice a, Lattice i, RS a, Eq i, Eq a, IC i) => Lattice (ExtResStringConstraint i a) where
    bottom = ExtResStringConstraint bottom bottom False
    top = ExtResStringConstraint top top False
    (ExtResStringConstraint r1 e1 False) `ljoin` (ExtResStringConstraint r2 e2 False)
        = ExtResStringConstraint (r1 `ljoin` r2) bottom False
    (ExtResStringConstraint r1 e1 False) `ljoin` (ExtResStringConstraint r2 e2 True)
        = ExtResStringConstraint (r1 `ljoin` r2) e2 True
    (ExtResStringConstraint r1 e1 True) `ljoin` (ExtResStringConstraint r2 e2 False)
        = ExtResStringConstraint (r1 `ljoin` r2) e1 True
    (ExtResStringConstraint r1 e1 True) `ljoin` (ExtResStringConstraint r2 e2 True)
        = ExtResStringConstraint (r1 `ljoin` r2)
            (exceptRSC ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2)) (r1 `ljoin` r2))  True
    (ExtResStringConstraint r1 e1 False) `meet` (ExtResStringConstraint r2 e2 False)
        = ExtResStringConstraint (r1 `meet` r2) bottom False
    (ExtResStringConstraint r1 e1 False) `meet` (ExtResStringConstraint r2 e2 True)
        = ExtResStringConstraint (r1 `meet` r2) (r1 `meet` e2) True
    (ExtResStringConstraint r1 e1 True) `meet` (ExtResStringConstraint r2 e2 False)
        = ExtResStringConstraint (r1 `meet` r2) (r2 `meet` e1) True
    (ExtResStringConstraint r1 e1 True) `meet` (ExtResStringConstraint r2 e2 True)
        = ExtResStringConstraint (r1 `meet` r2)
            (exceptRSC ((r1 `ljoin` e1) `meet` (r2 `ljoin` e2)) (r1 `meet` r2))  True


exceptRSC (ResStringConstraint i1 s1) (ResStringConstraint i2 s2)
    = ResStringConstraint (exceptIC i1 i2) (exceptPAC s1 s2)

exceptExtRSC (ExtResStringConstraint r1 e1 False) (ExtResStringConstraint r2 _ _)
    = ExtResStringConstraint (exceptRSC r1 r2) bottom False
exceptExtRSC (ExtResStringConstraint r1 e1 True) (ExtResStringConstraint r2 _ False)
    = ExtResStringConstraint (exceptRSC r1 r2)
                             (exceptRSC (exceptRSC e1 r2) (exceptRSC r1 r2)) True
exceptExtRSC (ExtResStringConstraint r1 e1 True) (ExtResStringConstraint r2 e2 True)
    = ExtResStringConstraint (exceptRSC r1 r2) (exceptRSC (exceptRSC e1 (r2 `ljoin` e2))
                                                          (exceptRSC r1 r2)) True
