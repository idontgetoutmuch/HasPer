data Z

data S n

data Nil = Empty
data a:*:l = a:*:l

-- Choices which have sizes. Note that we will only allow a size of 1 in a CHOICE.

data Phantom a = NoValue

data Choice :: * -> * -> * where
   CLift    :: a -> Choice a (S Z)
   CNil     :: Choice a Z
   CConsYes :: a -> Choice l n -> Choice (a:*:l) (S n)
   CConsNo  :: Phantom a -> Choice l n -> Choice (a:*:l) n

-- We would like tooMany and empty not to typecheck as CHOICEs because 
-- they have 2 choices and no choices respectively

tooMany = CConsYes (3::Integer) (CConsYes True CNil)

empty = CConsNo NoValue (CConsNo NoValue CNil) 

justRight1 = CConsYes (3::Integer) (CConsNo (NoValue::Phantom Bool) CNil)

justRight2 = CConsNo (NoValue::Phantom Integer) (CConsYes True CNil)

data TestType = MyInteger Integer | MyBool Bool

f (MyInteger x) = CConsYes x (CConsNo NoValue CNil)
f (MyBool x)    = CConsNo NoValue (CConsYes x CNil)

g x = CConsYes x (CConsNo NoValue CNil)

h x = CConsNo NoValue (CConsYes x CNil)

data ASNType :: * -> * where
   BOOLEAN         :: ASNType Bool
   INTEGER         :: ASNType Integer
   CHOICE          :: Choice a (S Z) -> ASNType a

-- Not quite what we need

toPer :: ASNType a -> a -> [Int]
toPer = undefined

shouldFail = toPer (CHOICE justRight1) (3:*:(True:*:Empty))

-- Better but gives the idea

toPer' :: ASNType a -> Choice a (S Z) -> [Int]
toPer' = undefined

-- This doesn't typecheck
-- shouldFail' = toPer' (CHOICE justRight1) tooMany

-- This doesn't typecheck
-- shouldFail'' = toPer' (CHOICE justRight1) empty

shouldCheck1 = toPer' (CHOICE justRight1) justRight1
shouldCheck2 = toPer' (CHOICE justRight1) justRight2

-- Finally what we want - it almost couldn't be simpler

data BSNType :: * -> * where
   BOOLEAN'         :: BSNType Bool
   INTEGER'         :: BSNType Integer
   CHOICE'          :: Dhoice a -> BSNType a

data Dhoice :: * -> * where
   DNil  :: Dhoice a 
   DCons :: BSNType a -> Dhoice l -> Dhoice (a:*:l) 

cType1 = CHOICE' (DCons INTEGER' (DCons BOOLEAN' DNil))

toQer :: BSNType a -> Choice a (S Z) -> [Int]
toQer = undefined

shouldCheck1' = toQer cType1 justRight1
shouldCheck2' = toQer cType1 justRight2

-- These fail to typecheck

-- shouldFail'' = toQer cType1 tooMany
-- shouldFail'' = toQer cType1 empty

-- This last line doesn't typecheck :-(

toRer :: BSNType a -> Choice a n -> [Int]
toRer BOOLEAN' (CLift False) = [0]
toRer BOOLEAN' (CLift True)  = [1]
-- toRer t@(CHOICE' c) x = toQer t x

data CSNType :: * -> * -> * where
   BOOLEAN''         :: CSNType Bool (S Z)
   INTEGER''         :: CSNType Integer (S Z)
   CHOICE''          :: Ehoice a n -> CSNType a n

data Ehoice :: * -> * -> *where
   ENil  :: Ehoice a (S Z)
   ECons :: CSNType a n -> Ehoice l n -> Ehoice (a:*:l) n

dType1 = CHOICE'' (ECons INTEGER'' (ECons BOOLEAN'' ENil))

toSer :: CSNType a n -> Choice a n -> [Int]
toSer = undefined

-- This is really what we want

data ASNType_ :: * -> * -> * where
   BOOLEAN_         :: ASNType_ Bool (S Z)
   INTEGER_         :: ASNType_ Integer (S Z)
   CHOICE_          :: Choice_ a n -> ASNType_ a n

data Choice_ :: * -> * -> *where
   CNil_  :: Choice_ a (S Z)
   CCons_ :: ASNType_ a n -> Choice_ l n -> Choice_ (a:*:l) n

type1_ = CHOICE_ (CCons_ INTEGER_ (CCons_ BOOLEAN_ CNil_))

data ASNValue_ :: * -> * -> * where
   CLift_    :: a -> ASNValue_ a (S Z)
   CEmpty_     :: ASNValue_ a Z
   CConsYes_ :: a -> ASNValue_ l n -> ASNValue_ (a:*:l) (S n)
   CConsNo_  :: Phantom a -> ASNValue_ l n -> ASNValue_ (a:*:l) n

tooMany_ = CConsYes_ (3::Integer) (CConsYes_ True CEmpty_)
tooMany'_ = CConsYes_ 3 (CConsYes_ True CEmpty_)

empty_ = CConsNo_ NoValue (CConsNo_ NoValue CEmpty_) 

justRight1_ = CConsYes_ (3::Integer) (CConsNo_ (NoValue::Phantom Bool) CEmpty_)
justRight1'_ = CConsYes_ 3 (CConsNo_ NoValue CEmpty_)

justRight2_ = CConsNo_ (NoValue::Phantom Integer) (CConsYes_ True CEmpty_)

toPer_ :: ASNType_ a n -> ASNValue_ a n -> [Int]
-- toPer_ = undefined
toPer_ BOOLEAN_ (CLift_ x) = toPer BOOLEAN x

