import Prelude hiding (mapM)
import Control.Applicative hiding (empty)
import Data.Foldable
import Data.Traversable
import Data.Monoid
import Control.Monad.State hiding (mapM)
import Text.PrettyPrint

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

testRelabel' t = let (p,_) = runState (mapM (\_ -> update) t) 0 in p

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

testSeq = SEQUENCE ((Cons (SEQUENCE (Cons BOOLEAN 2 (Cons INTEGER 1 Nil)))) 3 (Cons BOOLEAN 5 Nil))

data Foo :: * -> * -> * where
   BOOLEAN :: Foo Bool b
   INTEGER :: Foo Int b
   SEQUENCE :: Sequence a b -> Foo a b

pretty :: Show b => Foo a b -> Doc
pretty INTEGER = text "INTEGER"
pretty BOOLEAN = text "BOOLEAN"
pretty (SEQUENCE xs) = text "SEQUENCE" <+> parens (prettySeq xs)

prettySeq :: Show b => Sequence a b -> Doc
prettySeq Nil = text "Nil"
prettySeq (Cons x y xs)  = text "Cons" <+> parens (pretty x) <+> text (show y) <+> parens (prettySeq xs)

data Nil = Empty
data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs

data Sequence :: * -> * -> * where
   Nil :: Sequence Nil b
   Cons :: Foo a b -> b -> Sequence l b -> Sequence (a:*:l) b

fooMap :: (b -> c) -> Foo a b -> Foo a c
fooMap f INTEGER = INTEGER
fooMap f BOOLEAN = BOOLEAN
fooMap f (SEQUENCE xs) = SEQUENCE (sequenceMap f xs)

instance Functor (Foo a) where
   fmap = fooMap

fooFoldMap :: Monoid m => (b -> m) -> Foo a b -> m
fooFoldMap f INTEGER = mempty
fooFoldMap f BOOLEAN = mempty
fooFoldMap f (SEQUENCE xs) = sequenceFoldMap f xs

instance Foldable (Foo a) where
   foldMap = fooFoldMap

sequenceMap :: (b -> c) -> Sequence a b -> Sequence a c
sequenceMap f Nil = Nil
sequenceMap f (Cons x y xs) = Cons (fooMap f x) (f y) (sequenceMap f xs)

sequenceFoldMap :: Monoid m => (b -> m) -> Sequence a b -> m
sequenceFoldMap f Nil = mempty
sequenceFoldMap f (Cons x y xs) = (fooFoldMap f x) `mappend` (f y) `mappend` (sequenceFoldMap f xs)

fooTraverse :: Applicative f => (b -> f c) -> (Foo a b) -> f (Foo a c)
fooTraverse g INTEGER = pure INTEGER
fooTraverse g BOOLEAN = pure BOOLEAN
fooTraverse g (SEQUENCE xs) = SEQUENCE <$> sequenceTraverse g xs

instance Traversable (Foo a) where
   traverse = fooTraverse

sequenceTraverse :: Applicative f => (b -> f c) -> Sequence a b -> f (Sequence a c)
sequenceTraverse g Nil = pure Nil
sequenceTraverse g (Cons x y xs) = Cons <$> fooTraverse g x <*> g y <*> sequenceTraverse g xs

instance Show b => Show (Foo a b) where
   show x = render (pretty x)
