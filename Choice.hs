data Z

data S n

data Nil = Empty
data a:*:l = a:*:l

-- Choices which have sizes. Note that we will only allow a size of 1 in a CHOICE.

data Phantom a = NoValue

data Choice :: * -> * -> * where
   CNil     :: Choice a Z
   CConsYes :: a -> Choice l n -> Choice (a:*:l) (S n)
   CConsNo  :: Phantom a -> Choice l n -> Choice (a:*:l) n

-- We would like tooMany and empty not to typecheck as CHOICEs because 
-- they have 2 choices and no choices respectively

tooMany = CConsYes (3::Integer) (CConsYes True CNil)

empty = CConsNo NoValue (CConsNo NoValue CNil) 

justRight1 = CConsYes (3::Integer) (CConsNo (NoValue::Phantom Bool) CNil)

justRight2 = CConsNo (NoValue::Phantom Integer) (CConsYes True CNil)

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






