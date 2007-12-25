module Relabel where

import Prelude hiding (mapM)
import Control.Applicative hiding (empty)
import Data.Foldable
import Data.Traversable
import Data.Monoid
import Control.Monad.State hiding (mapM)
import Text.PrettyPrint
import ConstrainedType
import Language.ASN1 hiding (NamedType, BitString)
import Pretty

data Shadow :: * -> * -> * where
   SBOOLEAN   :: Shadow Bool b
   SINTEGER   :: Shadow Integer b
   SBITSTRING :: NamedBits -> Shadow BitString b
   SSEQUENCE  :: SSequence a b -> Shadow a b
   SCHOICE    :: SChoice a b -> Shadow (HL a (S Z)) b
   SSIZE      :: Shadow a b -> Constraint Integer -> EM Integer -> Shadow a b

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
shadow (BITSTRING bs) = SBITSTRING bs
shadow (SEQUENCE xs) = SSEQUENCE (shadowSequence xs)
shadow (CHOICE xs) = SCHOICE (shadowChoice xs)
shadow (SIZE t c em) = SSIZE (shadow t) c em

unShadow :: Shadow a TagValue -> ASNType a
unShadow SBOOLEAN = BOOLEAN
unShadow SINTEGER = INTEGER
unShadow (SBITSTRING bs) = BITSTRING bs
unShadow (SSEQUENCE xs) = SEQUENCE (unSSequence xs)
unShadow (SCHOICE xs) = CHOICE (unSChoice xs)
unShadow (SSIZE t c em) = SIZE (unShadow t) c em

shadowSequence :: Sequence a -> SSequence a TagValue
shadowSequence Nil = SNil
shadowSequence (Cons e s) = SCons (shadowElement e) (shadowSequence s)

shadowChoice :: Choice a -> SChoice a TagValue
shadowChoice NoChoice = SNoChoice
shadowChoice (ChoiceOption n cs) = SChoiceOption (shadowNamedType n) (shadowChoice cs)

unSSequence :: SSequence a TagValue -> Sequence a
unSSequence SNil = Nil
unSSequence (SCons se ss) = Cons (unSElement se) (unSSequence ss)

unSChoice :: SChoice a TagValue -> Choice a
unSChoice SNoChoice = NoChoice
unSChoice (SChoiceOption n cs) = ChoiceOption (unSNamedType n) (unSChoice cs)

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
shadowMap f (SBITSTRING bs) = SBITSTRING bs
shadowMap f (SSEQUENCE xs) = SSEQUENCE (sSequenceMap f xs)
shadowMap f (SCHOICE xs) = SCHOICE (sChoiceMap f xs)
shadowMap f (SSIZE t c em) = SSIZE (shadowMap f t) c em

sSequenceMap :: (b -> c) -> SSequence a b -> SSequence a c
sSequenceMap f SNil  = SNil
sSequenceMap f (SCons e s) = SCons (sElementMap f e) (sSequenceMap f s)

sChoiceMap :: (b -> c) -> SChoice a b -> SChoice a c
sChoiceMap f SNoChoice = SNoChoice
sChoiceMap f (SChoiceOption n cs) = SChoiceOption (sNamedTypeMap f n) (sChoiceMap f cs)

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
shadowFoldMap f (SBITSTRING bs) = mempty
shadowFoldMap f (SSEQUENCE xs) = sSequenceFoldMap f xs
shadowFoldMap f (SCHOICE xs) = sChoiceFoldMap f xs
shadowFoldMap f (SSIZE t c em) = shadowFoldMap f t

sSequenceFoldMap :: Monoid m => (b -> m) -> SSequence a b -> m
sSequenceFoldMap f SNil = mempty
sSequenceFoldMap f (SCons se ss) = (sElementFoldMap f se) `mappend` (sSequenceFoldMap f ss)

sChoiceFoldMap :: Monoid m => (b -> m) -> SChoice a b -> m
sChoiceFoldMap f SNoChoice = mempty
sChoiceFoldMap f (SChoiceOption n cs) = (sNamedTypeFoldMap f n) `mappend` (sChoiceFoldMap f cs)

sElementFoldMap :: Monoid m => (b -> m) -> SElementType a b -> m
sElementFoldMap f (SETMandatory snt) = sNamedTypeFoldMap f snt

sNamedTypeFoldMap :: Monoid m => (b -> m) -> SNamedType a b -> m
sNamedTypeFoldMap f (SNamedType n mti t) = (sTagInfoFoldMap f mti) `mappend` (shadowFoldMap f t)

sTagInfoFoldMap :: Monoid m => (b -> m) -> Maybe (STagInfo b) -> m
sTagInfoFoldMap = foldMap . g
   where g f (STagInfo tt tv tp) = f tv

instance Foldable (Shadow a) where
   foldMap = shadowFoldMap

shadowTraverse :: Applicative f => (b -> f c) -> Shadow a b -> f (Shadow a c)
shadowTraverse g SINTEGER = pure SINTEGER
shadowTraverse g SBOOLEAN = pure SBOOLEAN
shadowTraverse g (SBITSTRING bs) = SBITSTRING <$> pure bs
shadowTraverse g (SSEQUENCE xs) = SSEQUENCE <$> sSequenceTraverse g xs
shadowTraverse g (SCHOICE xs) = SCHOICE <$> sChoiceTraverse g xs
shadowTraverse g (SSIZE t c em) = SSIZE <$> shadowTraverse g t <*> pure c <*> pure em

sSequenceTraverse :: Applicative f => (b -> f c) -> SSequence a b -> f (SSequence a c)
sSequenceTraverse g SNil = pure SNil
sSequenceTraverse g (SCons se ss) = SCons <$> sElementTraverse g se <*> sSequenceTraverse g ss

sChoiceTraverse :: Applicative f => (b -> f c) -> SChoice a b -> f (SChoice a c)
sChoiceTraverse g SNoChoice = pure SNoChoice
sChoiceTraverse g (SChoiceOption n cs) = SChoiceOption <$> sNamedTypeTraverse g n <*> sChoiceTraverse g cs

sElementTraverse :: Applicative f => (b -> f c) -> SElementType a b -> f (SElementType a c)
sElementTraverse g (SETMandatory snt) = SETMandatory <$> sNamedTypeTraverse g snt

sNamedTypeTraverse :: Applicative f => (b -> f c) -> SNamedType a b -> f (SNamedType a c)
sNamedTypeTraverse g (SNamedType n mti t) = SNamedType <$> pure n <*> sTagInfoTraverse g mti <*> shadowTraverse g t

sTagInfoTraverse :: Applicative f => (b -> f c) -> Maybe (STagInfo b) -> f (Maybe (STagInfo c))
sTagInfoTraverse = traverse . g
   where g f (STagInfo tt tv tp) = STagInfo <$> pure tt <*> f tv <*> pure tp

instance Traversable (Shadow a) where
   traverse = shadowTraverse

update :: (Num a, MonadState a m) => m a
update =
   do x <- get
      put (x + 1)
      return x
   
relabel t = let (p,_) = runState (mapM (\_ -> update) t) 0 in p

