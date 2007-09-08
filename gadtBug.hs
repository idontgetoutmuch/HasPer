import Test.QuickCheck
import Text.PrettyPrint

data Type :: * -> * where
   INTEGER  :: Type Integer
   CHAR     :: Type Char
   SEQUENCE :: Sequence a -> Type a

data NamedType :: * -> * where
   NamedType :: String -> Type a -> NamedType a

data Sequence :: * -> * where
   Nil     :: Sequence Nil
   Cons    :: (Arbitrary a, Show a) => ElementType a -> Sequence l -> Sequence (a:*:l)

data Nil = Empty

data a:*:l = a:*:l

instance Show Nil where
   show _ = "Empty"

instance (Show a, Show l) => Show (a:*:l) where
   show (x:*:xs) = show x ++ ":*:" ++ show xs

instance Arbitrary Nil where
   arbitrary = return Empty

instance (Arbitrary a, Arbitrary l) => Arbitrary (a:*:l) where
   arbitrary =
      do x <- arbitrary
         y <- arbitrary
         return (x:*:y)

data ElementType :: * -> * where
   Mandatory :: NamedType a -> ElementType a

data RepNamedType = forall t . (Arbitrary t, Show t) => RepNamedType (NamedType t)

instance Arbitrary RepNamedType where
   arbitrary =
      do rct <- arbitrary
         case rct of
            RepType ct ->
               return (RepNamedType (NamedType "" ct))

data RepElementType = forall t . (Arbitrary t, Show t) => RepElementType (ElementType t)

instance Arbitrary RepElementType where
   arbitrary =
      do rnt <- arbitrary
         case rnt of
            RepNamedType nt ->
               return (RepElementType (Mandatory nt)) 

data RepSeq = forall t . (Arbitrary t, Show t) => RepSeq (Sequence t)

instance Arbitrary RepSeq where
   arbitrary =
      oneof [
         return (RepSeq Nil),
         do x  <- arbitrary
            xs <- arbitrary
            case x of
               RepType u ->
                  case xs of
                     RepSeq us ->
                        return (RepSeq (Cons (Mandatory (NamedType "" u)) us))
         ]

data RepType = forall t . (Arbitrary t, Show t) => RepType (Type t)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         return (RepType INTEGER),
         return (RepType CHAR),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepElementType u -> 
                  case y of
                     RepSeq v -> 
                        return (RepType (SEQUENCE (Cons u v)))
         ]

instance Show RepType where
   show r =
      case r of
         RepType t -> 
            render (prettyType t)

prettyType :: Type a -> Doc
prettyType INTEGER      = text "INTEGER"
prettyType CHAR         = text "CHAR"
prettyType (SEQUENCE s) = prettySequence s

prettySequence :: Sequence a -> Doc
prettySequence Nil = empty
prettySequence (Cons e l) = prettyElem e <> comma $$ prettySequence l

prettyElem :: ElementType a -> Doc
prettyElem (Mandatory n) = prettyNamedType n

prettyNamedType :: NamedType a -> Doc
prettyNamedType (NamedType n t) =
   text n <> text " ::= " <> prettyType t

data RepSeqVal = forall t . (Arbitrary t, Show t) => RepSeqVal (Sequence t) t

instance Show RepSeqVal where
   show r =
      case r of
         RepSeqVal s x ->
            render (prettySequence s <> space <> text (show x))

arbitrarySeq :: RepSeq -> Gen RepSeqVal
arbitrarySeq x =
   case x of
      (RepSeq y) ->
         case y of
            Nil -> 
               return (RepSeqVal y Empty)
            Cons t ts -> 
               do u <- arbitrary
                  return (RepSeqVal (Cons t Nil) (u:*:Empty))

instance Arbitrary RepSeqVal where
   arbitrary =
      do t <- arbitrary
         arbitrarySeq t
