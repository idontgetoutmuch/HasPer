{-# OPTIONS_GHC -XFlexibleInstances -XGADTs -XMultiParamTypeClasses
                -XFlexibleContexts -XFunctionalDependencies
#-}

module LatticeMod where

import Data.Char
import Data.List
import Control.Monad.Error
import ASNTYPE

data ConstructConstraint i = ConstructConstraint {constructConstraint :: i}
   deriving (Show, Eq)

class IntegerCon a where
    makeIntegerConstraint :: InfInteger -> InfInteger -> a
    getLower :: a -> InfInteger
    getUpper :: a -> InfInteger
    within :: a -> a -> Bool
    serialCombine :: a -> a -> a
    exceptIntegerConstraint :: a -> a -> a


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



-- These are similar to ExtResStringConstraint functions
getBSRC (ExtensibleConstraint r _ _) = r
getBSEC (ExtensibleConstraint _ e _) = e

instance IntegerCon IntegerConstraint where
    makeIntegerConstraint l u = IntegerConstraint l u
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
    exceptIntegerConstraint = exceptIntCon


instance IntegerCon ValidIntegerConstraint where
    makeIntegerConstraint l u = Valid [makeIntegerConstraint l u]
    getLower (Valid ls) = (getLower . head) ls
    getUpper (Valid ls) = (getUpper . last) ls
    within (Valid ls) (Valid []) = True
    within (Valid ls) (Valid (f:r))
        = or (map (flip within f) ls) && within (Valid ls) (Valid r)
    serialCombine (Valid ls) (Valid xs)
        = Valid (map (updateConstraintIC ls) xs)
          where
            updateConstraintIC (x:y) f
                | within x f = serialCombine x f
                | otherwise = updateConstraintIC y f
    exceptIntegerConstraint = exceptVIC


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


instance Lattice BooleanConstraint where
   bottom = BooleanConstraint []
   top = BooleanConstraint [False,True]
   (BooleanConstraint bs1) `ljoin` (BooleanConstraint bs2)
        = BooleanConstraint (union bs1 bs2)
   (BooleanConstraint bs1) `meet` (BooleanConstraint bs2)
        = BooleanConstraint (intersect bs1 bs2)


instance (IntegerCon i, Lattice i) => Lattice (ExtensibleConstraint i) where
   bottom = ExtensibleConstraint bottom bottom False
   top = ExtensibleConstraint top top False
   (ExtensibleConstraint r1 e1 False) `ljoin` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `ljoin` r2) bottom False
   (ExtensibleConstraint r1 e1 False) `ljoin` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `ljoin` r2) e2 True
   (ExtensibleConstraint r1 e1 True) `ljoin` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `ljoin` r2) e1 True
   (ExtensibleConstraint r1 e1 True) `ljoin` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `ljoin` r2)
            (exceptIntegerConstraint ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2)) (r1 `ljoin` r2))  True
   (ExtensibleConstraint r1 e1 False) `meet` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `meet` r2) bottom False
   (ExtensibleConstraint r1 e1 False) `meet` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `meet` r2) (r1 `meet` e2) True
   (ExtensibleConstraint r1 e1 True) `meet` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `meet` r2) (r2 `meet` e1) True
   (ExtensibleConstraint r1 e1 True) `meet` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `meet` r2)
            (exceptIntegerConstraint ((r1 `ljoin` e1) `meet` (r2 `ljoin` e2)) (r1 `meet` r2))  True

instance Lattice ValidIntegerConstraint where
   bottom = Valid [bottom]
   top = Valid [top]
   Valid ic1 `ljoin` Valid ic2
        = Valid (listUnion ic1 ic2)
   Valid a `meet` Valid b
      = Valid (listInter a b)

instance Lattice EnumeratedConstraint where
   bottom = EnumeratedConstraint []
   top = EnumeratedConstraint [0..]
   EnumeratedConstraint ic1 `ljoin` EnumeratedConstraint ic2
        = EnumeratedConstraint (union ic1 ic2)
   EnumeratedConstraint a `meet` EnumeratedConstraint b
      = EnumeratedConstraint (intersect a b)

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



lowerHalf x = IntegerConstraint NegInf (Val x)
upperHalf x = IntegerConstraint (Val x) PosInf


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



class ExtConstraint a where
    isExtensible :: a b -> Bool
    makeExtensibleConstraint :: b -> b -> Bool -> a b
    getRootConstraint   :: a b -> b
    getExtConstraint   :: a b -> b

class Constraint c where
    isValid :: c -> c -> Bool
    updateConstraint :: c -> c -> c
    except :: c -> c -> c

instance (IntegerCon i, Lattice a, RS a, Eq a)
    => Constraint (ResStringConstraint a i) where
    isValid x y  = lValidResCon x y
    updateConstraint x y = lUpdateResCon x y
    except      = exceptRSC

instance ExtConstraint ExtensibleConstraint where
    isExtensible = extensibleBS
    makeExtensibleConstraint x y b = ExtensibleConstraint x y b
    getRootConstraint x      = getBSRC x
    getExtConstraint x      = getBSEC x


instance Constraint BooleanConstraint where
    isValid (BooleanConstraint x) (BooleanConstraint y) = validCon x y
    updateConstraint (BooleanConstraint x) (BooleanConstraint y) = BooleanConstraint (intersect x y)
    except (BooleanConstraint x) (BooleanConstraint y)   = BooleanConstraint (x \\ y)

validCon x [] = True
validCon x (f:r)
        = elem f x && validCon x r
												
instance Constraint EnumeratedConstraint where
    isValid (EnumeratedConstraint x) (EnumeratedConstraint y) = validCon x y
    updateConstraint (EnumeratedConstraint x) (EnumeratedConstraint y) 
            = EnumeratedConstraint (intersect x y)
    except (EnumeratedConstraint x) (EnumeratedConstraint y)   
            = EnumeratedConstraint (x \\ y)
		
instance  Constraint IntegerConstraint where
    isValid x y  = within x y
    updateConstraint x y = serialCombine x y
    except x y   = exceptIntegerConstraint x y


instance  Constraint ValidIntegerConstraint where
    isValid x y  = within x y
    updateConstraint x y = serialCombine x y
    except x y   = exceptIntegerConstraint x y





lValidResCon :: (IntegerCon i, Lattice a, RS a, Eq a) =>
    ResStringConstraint a i -> ResStringConstraint a i -> Bool
lValidResCon (ResStringConstraint p1 s1) (ResStringConstraint p2 s2)
    = within s1 s2 && lValidPA p1 p2

lUpdateResCon :: (IntegerCon t, Lattice t1, RS t1, Eq t1) =>
                 ResStringConstraint t1 t
                 -> ResStringConstraint t1 t
                 -> ResStringConstraint t1 t
lUpdateResCon (ResStringConstraint p1 s1) (ResStringConstraint p2 s2)
     = ResStringConstraint (lUpdatePA p1 p2) (serialCombine s1 s2)

{- NOTE: Need y == top to deal with RCS constraints with only size constraint -}

lUpdatePA :: (Lattice a, RS a, Eq a) => a -> a -> a
lUpdatePA x y
    | x == bottom || y == bottom
        = bottom
    | y == top
        = x
    | otherwise
        = y

lValidPA :: (Lattice a, RS a, Eq a) => a -> a -> Bool
lValidPA x y
    = if x == top || y == top
        then True
        else and (map (flip elem (getString x)) (getString y))


extensible :: ExtensibleConstraint a -> Bool
extensible (ExtensibleConstraint _ _ b) = b

extensibleBS :: ExtensibleConstraint i -> Bool
extensibleBS (ExtensibleConstraint _ _ b) = b

getRSRC :: ExtensibleConstraint a -> a
getRSRC (ExtensibleConstraint r _ _) = r

getRSEC :: ExtensibleConstraint a -> a
getRSEC (ExtensibleConstraint _ e _) = e

getSizeConstraint :: ResStringConstraint a i -> i
getSizeConstraint (ResStringConstraint s i) = i

getPAConstraint :: RS a => ResStringConstraint a i -> a
getPAConstraint (ResStringConstraint s i) = s

instance (Lattice a, Lattice i,RS a, Eq a, Eq i, IntegerCon i) => Lattice (ResStringConstraint a i) where
    bottom = ResStringConstraint bottom bottom
    top = ResStringConstraint top top
    (ResStringConstraint s1 i1) `ljoin` (ResStringConstraint s2 i2)
        = ResStringConstraint (s1 `ljoin` s2) (i1 `ljoin` i2)
    (ResStringConstraint s1 i1) `meet` (ResStringConstraint s2 i2)
        = ResStringConstraint (s1 `meet` s2) (i1 `meet` i2)


instance (RS a, IntegerCon i, Lattice (ResStringConstraint a i))
    => Lattice (ExtensibleConstraint (ResStringConstraint a i)) where
    bottom = ExtensibleConstraint bottom bottom False
    top = ExtensibleConstraint top top False
    (ExtensibleConstraint r1 e1 False) `ljoin` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `ljoin` r2) bottom False
    (ExtensibleConstraint r1 e1 False) `ljoin` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `ljoin` r2) e2 True
    (ExtensibleConstraint r1 e1 True) `ljoin` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `ljoin` r2) e1 True
    (ExtensibleConstraint r1 e1 True) `ljoin` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `ljoin` r2)
            (exceptRSC ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2)) (r1 `ljoin` r2))  True
    (ExtensibleConstraint r1 e1 False) `meet` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `meet` r2) bottom False
    (ExtensibleConstraint r1 e1 False) `meet` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `meet` r2) (r1 `meet` e2) True
    (ExtensibleConstraint r1 e1 True) `meet` (ExtensibleConstraint r2 e2 False)
        = ExtensibleConstraint (r1 `meet` r2) (r2 `meet` e1) True
    (ExtensibleConstraint r1 e1 True) `meet` (ExtensibleConstraint r2 e2 True)
        = ExtensibleConstraint (r1 `meet` r2)
            (exceptRSC ((r1 `ljoin` e1) `meet` (r2 `ljoin` e2)) (r1 `meet` r2))  True

exceptRSC (ResStringConstraint s1 i1) (ResStringConstraint s2 i2)
    = ResStringConstraint (exceptPAC s1 s2) (exceptIntegerConstraint i1 i2)
