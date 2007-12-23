import Prelude hiding (mapM)
import Control.Applicative hiding (empty)
import Data.Foldable
import Data.Traversable
import Data.Monoid
import Control.Monad.State hiding (mapM)
import Text.PrettyPrint
import ConstrainedType
import Language.ASN1 hiding (NamedType)
import Pretty

data Shadow :: * -> * -> * where
   SBOOLEAN :: Shadow Bool b
   SINTEGER :: Shadow Integer b
   SSEQUENCE :: SSequence a b -> Shadow a b
   SCHOICE   :: SChoice a b -> Shadow (HL a (S Z)) b

data SSequence :: * -> * -> * where
   SNil     :: SSequence Nil b
   SCons    :: SElementType a b -> SSequence l b -> SSequence (a:*:l) b

data SChoice :: * -> * -> * where
    SNoChoice     :: SChoice Nil b
    SChoiceOption :: SNamedType a b -> SChoice l b -> SChoice (a:*:l) b

data SElementType :: * -> * -> * where
   SETMandatory :: SNamedType a b -> SElementType a b

data SNamedType :: * -> * -> * where
   SNamedType :: Name -> Maybe (STagInfo b) -> Shadow a b -> SNamedType a b

data STagInfo b = STagInfo TagType b TagPlicity

shadow :: ASNType a -> Shadow a TagValue
shadow BOOLEAN = SBOOLEAN
shadow INTEGER = SINTEGER
shadow (SEQUENCE xs) = SSEQUENCE (shadowSequence xs)

unShadow :: Shadow a TagValue -> ASNType a
unShadow SBOOLEAN = BOOLEAN
unShadow SINTEGER = INTEGER
unShadow (SSEQUENCE xs) = SEQUENCE (unSSequence xs)

shadowSequence :: Sequence a -> SSequence a TagValue
shadowSequence Nil = SNil
shadowSequence (Cons e s) = SCons (shadowElement e) (shadowSequence s)

unSSequence :: SSequence a TagValue -> Sequence a
unSSequence SNil = Nil
unSSequence (SCons se ss) = Cons (unSElement se) (unSSequence ss)

shadowElement :: ElementType a -> SElementType a TagValue
shadowElement (ETMandatory n) = SETMandatory (shadowNamedType n)

unSElement :: SElementType a TagValue -> ElementType a
unSElement (SETMandatory n) = ETMandatory (unSNamedType n)

shadowNamedType :: NamedType a -> SNamedType a TagValue
shadowNamedType (NamedType n Nothing at) = SNamedType n Nothing (shadow at)
shadowNamedType (NamedType n (Just (tt, tv, tp)) at) = SNamedType n (Just (STagInfo tt tv tp)) (shadow at)

unSNamedType :: SNamedType a TagValue -> NamedType a
unSNamedType (SNamedType n Nothing s) = NamedType n Nothing (unShadow s)
unSNamedType (SNamedType n (Just (STagInfo tt tv tp)) s) = NamedType n (Just (tt, tv, tp)) (unShadow s)

shadowMap :: (b -> c) -> Shadow a b -> Shadow a c
shadowMap f SBOOLEAN = SBOOLEAN
shadowMap f SINTEGER = SINTEGER
shadowMap f (SSEQUENCE xs) = SSEQUENCE (sSequenceMap f xs)

sSequenceMap :: (b -> c) -> SSequence a b -> SSequence a c
sSequenceMap f SNil  = SNil
sSequenceMap f (SCons e s) = SCons (sElementMap f e) (sSequenceMap f s)

sElementMap :: (b -> c) -> SElementType a b -> SElementType a c
sElementMap f (SETMandatory n) = SETMandatory (sNamedTypeMap f n)

sNamedTypeMap :: (b -> c) -> SNamedType a b -> SNamedType a c
sNamedTypeMap f (SNamedType n mti t) = SNamedType n (sTagInfoMap f mti) (shadowMap f t)

sTagInfoMap :: (b -> c) -> Maybe (STagInfo b) -> Maybe (STagInfo c)
sTagInfoMap = fmap . g
   where g f (STagInfo tt tv tp) = STagInfo tt (f tv) tp

instance Functor (Shadow a) where
   fmap = shadowMap

shadowFoldMap :: Monoid m => (b -> m) -> Shadow a b -> m
shadowFoldMap f SINTEGER = mempty
shadowFoldMap f SBOOLEAN = mempty
shadowFoldMap f (SSEQUENCE xs) = sSequenceFoldMap f xs

sSequenceFoldMap :: Monoid m => (b -> m) -> SSequence a b -> m
sSequenceFoldMap f SNil = mempty
sSequenceFoldMap f (SCons se ss) = (sElementFoldMap f se) `mappend` (sSequenceFoldMap f ss)

sElementFoldMap :: Monoid m => (b -> m) -> SElementType a b -> m
sElementFoldMap f (SETMandatory snt) = sNamedTypeFoldMap f snt

sNamedTypeFoldMap :: Monoid m => (b -> m) -> SNamedType a b -> m
sNamedTypeFoldMap f (SNamedType n mti t) = (sTagInfoFoldMap f mti) `mappend` (shadowFoldMap f t)

sTagInfoFoldMap :: Monoid m => (b -> m) -> Maybe (STagInfo b) -> m
sTagInfoFoldMap = foldMap . g
   where g f (STagInfo tt tv tp) = f tv

instance Foldable (Shadow a) where
   foldMap = shadowFoldMap

testMap = prettyType . unShadow . fmap (+1) . shadow

testFold = undefined

n1 =ETMandatory (NamedType "Baz" (Just (Context, 7, Implicit)) BOOLEAN)

seq1 = Cons (ETMandatory (NamedType "Foo" (Just (Context, 3, Implicit)) BOOLEAN)) Nil

seq2 = Cons (ETMandatory (NamedType "Bar" (Just (Context, 5, Implicit)) INTEGER)) Nil

seq3 = Cons n1 seq1

seq4 = Cons n1 seq3

seq5 = Cons n1 seq2

n2 = ETMandatory (NamedType "Faz" (Just (Context, 11, Implicit)) (SEQUENCE seq5))

testType1 = SEQUENCE (Cons (ETMandatory (NamedType "Foo" (Just (Context, 3, Implicit)) BOOLEAN)) Nil)

testType2 = SEQUENCE (Cons n1 seq2)

testType3 = SEQUENCE seq4

testType4 = SEQUENCE (Cons n2 seq5)

update :: MonadState Int m => m Int
update =
   do x <- get
      put (x + 1)
      return x
   
testRelabel t = let (p,_) = runState (mapM (\_ -> update) t) 0 in p

testSeq = MYSEQUENCE ((MyCons (MYSEQUENCE (MyCons MYBOOLEAN 2 (MyCons MYINTEGER 1 MyNil)))) 3 (MyCons MYBOOLEAN 5 MyNil))

data Blag :: * -> * -> * where
   MYBOOLEAN :: Blag Bool b
   MYINTEGER :: Blag Int b
   MYSEQUENCE :: MySequence a b -> Blag a b

pretty' :: Show b => Blag a b -> Doc
pretty' MYINTEGER = text "MYINTEGER"
pretty' MYBOOLEAN = text "MYBOOLEAN"
pretty' (MYSEQUENCE xs) = text "MYSEQUENCE" <+> parens (prettySeq' xs)

prettySeq' :: Show b => MySequence a b -> Doc
prettySeq' MyNil = text "MyNil"
prettySeq' (MyCons x y xs)  = text "MyCons" <+> parens (pretty' x) <+> text (show y) <+> parens (prettySeq' xs)

data MyNil = Empty
data a:+:l = a:+:l

instance Show MyNil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:+:l) where
   show (x:+:xs) = show x ++ ":+:" ++ show xs

data MySequence :: * -> * -> * where
   MyNil :: MySequence MyNil b
   MyCons :: Blag a b -> b -> MySequence l b -> MySequence (a:*:l) b

fooMap :: (b -> c) -> Blag a b -> Blag a c
fooMap f MYINTEGER = MYINTEGER
fooMap f MYBOOLEAN = MYBOOLEAN
fooMap f (MYSEQUENCE xs) = MYSEQUENCE (sequenceMap f xs)

instance Functor (Blag a) where
   fmap = fooMap

fooFoldMap :: Monoid m => (b -> m) -> Blag a b -> m
fooFoldMap f MYINTEGER = mempty
fooFoldMap f MYBOOLEAN = mempty
fooFoldMap f (MYSEQUENCE xs) = sequenceFoldMap f xs

instance Foldable (Blag a) where
   foldMap = fooFoldMap

sequenceMap :: (b -> c) -> MySequence a b -> MySequence a c
sequenceMap f MyNil = MyNil
sequenceMap f (MyCons x y xs) = MyCons (fooMap f x) (f y) (sequenceMap f xs)

sequenceFoldMap :: Monoid m => (b -> m) -> MySequence a b -> m
sequenceFoldMap f MyNil = mempty
sequenceFoldMap f (MyCons x y xs) = (fooFoldMap f x) `mappend` (f y) `mappend` (sequenceFoldMap f xs)

fooTraverse :: Applicative f => (b -> f c) -> (Blag a b) -> f (Blag a c)
fooTraverse g MYINTEGER = pure MYINTEGER
fooTraverse g MYBOOLEAN = pure MYBOOLEAN
fooTraverse g (MYSEQUENCE xs) = MYSEQUENCE <$> sequenceTraverse g xs

instance Traversable (Blag a) where
   traverse = fooTraverse

sequenceTraverse :: Applicative f => (b -> f c) -> MySequence a b -> f (MySequence a c)
sequenceTraverse g MyNil = pure MyNil
sequenceTraverse g (MyCons x y xs) = MyCons <$> fooTraverse g x <*> g y <*> sequenceTraverse g xs

instance Show b => Show (Blag a b) where
   show x = render (pretty' x)
