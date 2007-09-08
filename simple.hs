import Test.QuickCheck
import Text.PrettyPrint

data Type :: * -> * where
   INTEGER  :: Type Integer
   CHAR     :: Type Char
   SEQUENCE :: Sequence a -> Type a

data Sequence :: * -> * where
   Nil     :: Sequence Nil
   Cons    :: Type a -> Sequence l -> Sequence (a:*:l)

data Nil = Empty

data a:*:l = a:*:l

prettyType :: Type a -> Doc
prettyType INTEGER      = text "INTEGER"
prettyType CHAR         = text "CHAR"
prettyType (SEQUENCE s) = 
   text "SEQUENCE" <+> braces (prettySequence s)

data RepType = forall a . RepType (Type a)

instance Arbitrary RepType where
   arbitrary =
      oneof [
         return (RepType INTEGER),
         return (RepType CHAR),
         do x <- arbitrary
            y <- arbitrary
            case x of
               RepType u -> 
                  case y of
                     RepSeq v -> 
                        return (RepType (SEQUENCE (Cons u v)))
         ]

instance Show RepType where
   show t =
      case t of
         (RepType u) ->
            render (prettyType u)

prettySequence :: Sequence a -> Doc
prettySequence Nil = empty
prettySequence (Cons x Nil) =
   prettyType x
prettySequence (Cons e l) = prettyType e <> comma $$ prettySequence l

data RepSeq = forall t . RepSeq (Sequence t)

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
                        return (RepSeq (Cons u us))
         ]

prettySeqVal :: Sequence a -> a -> Doc
prettySeqVal Nil _ = empty
prettySeqVal (Cons e Nil) (x:*:Empty) =
   prettyTypeVal e x
prettySeqVal (Cons e l) (x:*:xs) =
   prettyTypeVal e x <> comma $$ prettySeqVal l xs 

data RepSeqVal = forall a . RepSeqVal (Sequence a) a

arbitrarySeq :: Sequence a -> Gen RepSeqVal
arbitrarySeq Nil = 
   return (RepSeqVal Nil Empty)
arbitrarySeq (Cons t ts) =
   do u <- arbitraryType t
      us <- arbitrarySeq ts
      case u of
         RepTypeVal a v ->
            case us of
               RepSeqVal bs vs ->
                  return (RepSeqVal (Cons a bs) (v:*:vs))

arbitraryType :: Type a -> Gen RepTypeVal
arbitraryType INTEGER =
   do n <- arbitrary
      return (RepTypeVal INTEGER n)
arbitraryType CHAR =
   do c <- arbitrary
      return (RepTypeVal CHAR c)
arbitraryType (SEQUENCE s) =
   do r <- arbitrarySeq s
      case r of
         RepSeqVal as vs ->
            return (RepTypeVal (SEQUENCE as) vs)

prettyTypeVal :: Type a -> a -> Doc
prettyTypeVal  INTEGER x     = text "INTEGER" <> colon <+> text (show x)
prettyTypeVal  CHAR    x     = text "CHAR" <> colon <+> text [x]
prettyTypeVal (SEQUENCE s) x = text "SEQUENCE" <+> braces (prettySeqVal s x)

data RepTypeVal = forall a . RepTypeVal (Type a) a

instance Show RepTypeVal where
   show x =
      case x of
         RepTypeVal t y ->
            render (prettyTypeVal t y)

instance Arbitrary RepTypeVal where
   arbitrary =
      do x <- arbitrary
         case x of
            RepType t ->
               arbitraryType t
               