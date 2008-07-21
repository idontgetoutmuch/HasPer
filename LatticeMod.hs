{-# OPTIONS_GHC -XFlexibleInstances #-}

module LatticeMod where

class Lattice a where
   bottom, top :: a
   meet, ljoin  :: a -> a -> a

data LatConstraint = Bottom | LatConstraint InfInteger InfInteger | Top
   deriving (Show, Eq)

{-
data MyLatConstraint = MyLatConstraint InfInteger InfInteger
   deriving (Show, Eq)
-}

data MyLatConstraint = MyLatConstraint {lower :: InfInteger, upper :: InfInteger}
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


instance Lattice LatConstraint where
   bottom = Bottom
   top = Top
   Top `meet` y = top
   Bottom `meet` y = y
   (LatConstraint l1 u1) `meet` (LatConstraint l2 u2) = LatConstraint (min l1 l2) (max u1 u2)
   (LatConstraint l1 u1) `ljoin` (LatConstraint l2 u2)
      | u2 < l1   = bottom
      | l2 > u2   = bottom
      | otherwise = LatConstraint (max l1 l2) (min u1 u2)
   Bottom `ljoin` x = bottom
   x `ljoin` Bottom = bottom
   Top `ljoin` Top  = Top
   Top `ljoin` x@(LatConstraint l u) = x
   x@(LatConstraint l u) `ljoin` Top = x


instance Lattice MyLatConstraint where
   bottom = MyLatConstraint PosInf NegInf
   top = MyLatConstraint NegInf PosInf
   (MyLatConstraint l1 u1) `meet` (MyLatConstraint l2 u2) = MyLatConstraint (min l1 l2) (max u1 u2)
   (MyLatConstraint l1 u1) `ljoin` (MyLatConstraint l2 u2)
      | u2 < l1   = bottom
      | l2 > u2   = bottom
      | otherwise = MyLatConstraint (max l1 l2) (min u1 u2)

lowerHalf x = MyLatConstraint NegInf (V x)
upperHalf x = MyLatConstraint (V x) PosInf

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


testReal :: Either String LatConstraint
testReal = (Right (LatConstraint (V 3) (V 7))) `ljoin` (Right (LatConstraint (V 5) (V 6)))


exceptTest = latExcept Top (LatConstraint (V 5) (V 12))
exceptTest2 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint (V 5) (V 12))
exceptTest3 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint (V 5) PosInf)
exceptTest4 = latExcept (LatConstraint (V 1) PosInf) (LatConstraint PosInf PosInf)
