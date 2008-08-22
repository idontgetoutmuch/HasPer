{-# OPTIONS_GHC -XFlexibleInstances -XGADTs  #-}

module LatticeMod where

import Data.List
import Language.ASN1

class Lattice a where
   bottom, top :: a
   meet, ljoin  :: a -> a -> a

data LatConstraint = Bottom | LatConstraint InfInteger InfInteger | Top
   deriving (Show, Eq)

{-
data IntegerConstraint = IntegerConstraint InfInteger InfInteger
   deriving (Show, Eq)
-}

data IntegerConstraint = IntegerConstraint {lower :: InfInteger, upper :: InfInteger}
   deriving (Show, Eq)


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

instance Lattice LatConstraint where
   bottom = Bottom
   top = Top
   Top `meet` y = top
   Bottom `meet` y = y
   (LatConstraint l1 u1) `meet` (LatConstraint l2 u2) = LatConstraint (min l1 l2) (max u1 u2)
   (LatConstraint l1 u1) `ljoin` (LatConstraint l2 u2)
      | u2 < l1   = bottom
      | l2 > u1   = bottom
      | otherwise = LatConstraint (max l1 l2) (min u1 u2)
   Bottom `ljoin` x = bottom
   x `ljoin` Bottom = bottom
   Top `ljoin` Top  = Top
   Top `ljoin` x@(LatConstraint l u) = x
   x@(LatConstraint l u) `ljoin` Top = x


instance Lattice IntegerConstraint where
   bottom = IntegerConstraint PosInf NegInf
   top = IntegerConstraint NegInf PosInf
   (IntegerConstraint l1 u1) `ljoin` {-`meet`-} (IntegerConstraint l2 u2)
        = IntegerConstraint (min l1 l2) (max u1 u2)
   (IntegerConstraint l1 u1) `meet` {-`ljoin`-} (IntegerConstraint l2 u2)
      | u2 < l1   = bottom
      | l2 > u1   = bottom
      | otherwise = IntegerConstraint (max l1 l2) (min u1 u2)




lowerHalf x = IntegerConstraint NegInf (V x)
upperHalf x = IntegerConstraint (V x) PosInf

getLower (IntegerConstraint l _) = l
getUpper (IntegerConstraint _ u) = u

exceptIC a@(IntegerConstraint l1 u1) (IntegerConstraint l2 u2)
    = if l1 < l2 && u1 > u2
        then a
        else if l1 < l2
            then IntegerConstraint l1 (l2-1)
            else if u1 > u2
                then IntegerConstraint (u2+1) u1
                else bottom

-- Can use \\ here since no repetition in permitted string
exceptPAC :: RS a => a -> a -> a
exceptPAC a b
    = let s1 = getString a
          s2 = getString b
      in putString (s1 \\ s2)

instance Lattice a => Lattice (Either String a) where
   bottom = Right bottom
   top    = Right top
   (Left s)  `meet` _          = Left s
   _         `meet` (Left s)   = Left s
   (Right x) `meet` (Right y)  = Right (x `meet` y)
   (Left s)  `ljoin` _         = Left s
   _         `ljoin` (Left s)  = Left s
   (Right x) `ljoin` (Right y) = Right (x `ljoin` y)

latExcept Top Top = bottom
latExcept Top Bottom = Top
latExcept Bottom _ = Bottom
latExcept Top y@(LatConstraint l2 u2)
    | l2 == NegInf = LatConstraint (u2 + V 1) PosInf
    | u2 == PosInf = LatConstraint NegInf (l2 - V 1)
    | otherwise = top
latExcept x@(LatConstraint l1 u1) y@(LatConstraint l2 u2)
    | x `ljoin` y == bottom = x
    | x `meet`  y == y      = bottom
    | x `meet` y  == x && l2 > l1 && u1 > u2
                            = x
    | l1 < l2 && u1 > u2    = x
    | l1 >=l2               = LatConstraint (u2 + (V 1)) u1
    | otherwise             = LatConstraint l1 (l2 - (V 1))


instance Lattice VisibleString where
    bottom = VisibleString ""
    top = VisibleString [' '..'~']
    (VisibleString s1) `meet` (VisibleString s2) = VisibleString (unionString s1 s2)
    (VisibleString s1) `ljoin` (VisibleString s2) = VisibleString (interString s1 s2)


unionString [] s = s
unionString (f:r) s = if elem f s
            then unionString r s
            else f : unionString r s

interString [] s = []
interString (f:r) s = if elem f s
            then f : interString r s
            else interString r s



class RS a where
    getString :: a -> String
    putString :: String -> a
    exceptRS :: a -> a -> a
    exceptRS = exceptPAC

instance RS VisibleString where
    getString (VisibleString s) = s
    putString s = VisibleString s


data ResStringConstraint a = ResStringConstraint IntegerConstraint a
    deriving (Show,Eq)
data ExtResStringConstraint a
    = ExtResStringConstraint (ResStringConstraint a) (ResStringConstraint a) Bool
    deriving (Show,Eq)
extensible :: (ExtResStringConstraint a) -> Bool
extensible (ExtResStringConstraint _ _ b) = b

getRC :: (ExtResStringConstraint a) -> ResStringConstraint a
getRC (ExtResStringConstraint r _ _) = r

getEC :: (ExtResStringConstraint a) -> ResStringConstraint a
getEC (ExtResStringConstraint _ e _) = e

getSC :: ResStringConstraint a -> IntegerConstraint
getSC (ResStringConstraint i s) = i

getPAC :: ResStringConstraint a -> a
getPAC (ResStringConstraint i s) = s

instance (Lattice a, RS a, Eq a) => Lattice (ResStringConstraint a) where
    bottom = ResStringConstraint bottom bottom
    top = ResStringConstraint top top
    (ResStringConstraint i1 s1) `ljoin` (ResStringConstraint i2 s2)
        = if (s1 == bottom && i2 == bottom) || (i1 == bottom && s2 == bottom)
               then top
               else ResStringConstraint (i1 `ljoin` i2) (s1 `ljoin` s2)
    (ResStringConstraint i1 s1) `meet` (ResStringConstraint i2 s2)
        = ResStringConstraint (i1 `meet` i2) (s1 `meet` s2)


instance (Lattice a, RS a, Eq a) => Lattice (ExtResStringConstraint a) where
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


testReal :: Either String LatConstraint
testReal = (Right (LatConstraint (V 3) (V 7))) `ljoin` (Right (LatConstraint (V 5) (V 6)))


exceptTest = latExcept Top (LatConstraint (V 5) (V 12))
exceptTest2 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint (V 5) (V 12))
exceptTest3 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint (V 5) PosInf)
exceptTest4 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint PosInf PosInf)
