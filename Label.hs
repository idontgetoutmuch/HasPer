import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Monoid
import Control.Monad.State

update :: MonadState Int m => m Int
update =
   do x <- get
      put (x + 1)
      return x
   
data Rose' a = Rose' a [Rose' a]
   deriving Show

instance Functor Rose' where
   fmap f (Rose' x rs) = Rose' (f x) (fmap (fmap f) rs)

instance Foldable Rose' where
   foldMap f (Rose' x rs) =  f x `mappend` (foldMap (foldMap f) rs)

instance Traversable Rose' where
   traverse f (Rose' x xs) = Rose' <$> f x <*> traverse (traverse f) xs

testTree = Rose' 3 [Rose' 5 [Rose' 11 [Rose' 19 []], Rose' 13 [], Rose' 17[]], Rose' 7 []]

testRelabel t = let (p,_) = runState ((Data.Traversable.mapM (\_ -> update)) t) 0 in p

data LRose a = LRose a String [LRose a]
   deriving Show

instance Functor LRose where
   fmap f (LRose x l rs) = LRose (f x) l (fmap (fmap f) rs)

instance Foldable LRose where
   foldMap f (LRose x l rs) =  f x `mappend` (foldMap (foldMap f) rs)

instance Traversable LRose where
   traverse f (LRose x l xs) = LRose <$> f x <*> pure l <*> traverse (traverse f) xs

testLTree = 
   LRose 3 "Three" [
      LRose 5 "Five" [
         LRose 11 "Eleven" [
            LRose 19 "Nineteen" []
            ], 
         LRose 13 "Thirteen" [],
         LRose 17 "Seventeen" []
         ], 
      LRose 7 "Seven" []]

testLTree1 =
   LRose 3 "Three" [
      LRose 5 "Five" [
         LRose 11 "Eleven" [],
         LRose 13 "Thirteen" []
         ],
      LRose 7 "Seven" [
         LRose 17 "Seventeen" [],
         LRose 19 "Nineteen" []
         ]
      ]

testLRelabel t = let (p,_) = runState ((Data.Traversable.mapM (\_ -> update)) t) 0 in p

