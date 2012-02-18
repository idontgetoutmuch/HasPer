{-# OPTIONS_GHC -XGADTs -fwarn-incomplete-patterns #-}

-- -fwarn-incomplete-patterns

module Pretty where

import ASNTYPE
import Language.ASN1 (
   -- TagPlicity (..),
   TagType (..)
   )
import Text.PrettyPrint as PP

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Map as Map

import NewTestData -- FIXME: For temporary testing - testing should
                   -- really be done outside of the module being tested

type ASNPrettyM = StateT (Map.Map TypeReference Doc) Identity

prettyTypeNonM :: ASNType a -> Doc
prettyTypeNonM t = vcat $ d:(map (\(k, v) -> text (ref k) <+> text "::=" <+> v) $ Map.toList m)
    where
      (d, m) = runIdentity . flip (runStateT . prettyType) Map.empty $ t

prettyNamedType :: NamedType a -> ASNPrettyM Doc
prettyNamedType (NamedType n ct) = do d <-  prettyType ct
                                      return $ text n <+> d

prettyChoice :: Choice a -> ASNPrettyM Doc
prettyChoice EmptyChoice                   = return $ PP.empty
prettyChoice (ChoiceOption nt EmptyChoice) = prettyNamedType nt
prettyChoice (ChoiceOption nt xs) = do
   d1 <- prettyNamedType nt
   d2 <- prettyChoice xs
   return $ vcat [d1 <> comma, d2]
prettyChoice (ChoiceExtensionMarker x) = do
   d <- prettyChoice x
   return $ vcat [text "..." <> comma, d <> comma]
-- FIXME: What should we do with v?
prettyChoice (ChoiceExtensionAdditionGroup v x) =
   liftM (brackets . brackets) $ prettyChoice' x

prettyChoice' :: Choice' a -> ASNPrettyM Doc
prettyChoice' EmptyChoice'                    = return $ PP.empty
prettyChoice' (ChoiceOption' nt EmptyChoice') = prettyNamedType nt
prettyChoice' (ChoiceOption' nt xs) = do
   do d1 <- prettyNamedType nt
      d2 <- prettyChoice' xs
      return $ vcat [d1 <> comma, d2]
prettyChoice' ChoiceExtensionMarker' = return $ text "..."

prettyType :: ASNType a -> ASNPrettyM Doc
prettyType (ReferencedType  r  t) = prettyReferencedType r t
prettyType (BuiltinType       bt) = prettyBuiltinType  bt
prettyType (ConstrainedType t  e) = do d1 <- prettyType t
                                       d2 <- prettyElementSetSpecs t e
                                       return $ d1 <+> parens d2

prettySeq :: Sequence a -> ASNPrettyM Doc
prettySeq EmptySequence                  = return $ PP.empty
prettySeq (AddComponent x EmptySequence) = prettyComponentType x
prettySeq (AddComponent x xs)            = do d  <- prettyComponentType x
                                              ds <- prettySeq xs
                                              return $ vcat [d <> comma, ds]
prettySeq (ExtensionMarker x)            = do d <- prettySeq x
                                              return $ vcat [text "..." <> comma, d <> comma]
-- FIXME: What should we do with v?
prettySeq (ExtensionAdditionGroup v x y) = do d1 <- prettySeq2 x
                                              d2 <- prettySeq y
                                              return $ vcat [(brackets $ brackets d1) <> comma, d2]

prettySeq2 :: Sequence' a -> ASNPrettyM Doc
prettySeq2 EmptySequence'                   = return $ PP.empty
prettySeq2 (AddComponent' x EmptySequence') = prettyComponentType x
prettySeq2 (AddComponent' x xs)             = do d1 <- prettyComponentType x
                                                 d2 <- prettySeq2 xs
                                                 return $ vcat [d1 <> comma, d2]

prettySeq' :: Sequence a -> ASNPrettyM [Doc]
prettySeq' EmptySequence       = return []
prettySeq' (AddComponent x xs) = do d  <- prettyComponentType x
                                    ds <- prettySeq' xs
                                    return (d:ds)
prettySeq' (ExtensionMarker x) = do ds <- prettySeq' x
                                    return $ (text "..."):ds
-- FIXME: What should we do with v?
prettySeq' (ExtensionAdditionGroup v x y) = do
   d1s <- prettySeq2' x
   d2s <- prettySeq' y
   return $ (brackets $ brackets $ vcat $ punctuate comma d1s):d2s

prettySeq2' :: Sequence' a -> ASNPrettyM [Doc]
prettySeq2' EmptySequence'       = return []
prettySeq2' (AddComponent' x xs) = do d  <- prettyComponentType x
                                      ds <- prettySeq2' xs
                                      return $ d:ds

prettySeq'' :: Sequence a -> ASNPrettyM Doc
prettySeq'' x = liftM (vcat . punctuate comma) $ prettySeq' x

prettyComponentType :: ComponentType a -> ASNPrettyM Doc
prettyComponentType (MandatoryComponent m)   = prettyNamedType m
prettyComponentType (OptionalComponent  m)   = do d <- prettyNamedType m
                                                  return $ d <+> text "OPTIONAL"
prettyComponentType (DefaultComponent m@(NamedType _ n) v) = do d <- prettyNamedType m
                                                                return $ d <+> text "DEFAULT" -- <+> prettyTypeVal n v

prettyBuiltinType :: ASNBuiltin a -> ASNPrettyM Doc
prettyBuiltinType (BITSTRING [])        = return $ text "BIT STRING"
prettyBuiltinType INTEGER               = return $ text "INTEGER"
prettyBuiltinType PRINTABLESTRING       = return $ text "PrintableString"
prettyBuiltinType BOOLEAN               = return $ text "BOOLEAN"
prettyBuiltinType IA5STRING             = return $ text "IA5STRING"
prettyBuiltinType (CHOICE c)            = do d <- prettyChoice c
                                             return $ text "CHOICE" <+> braces d
prettyBuiltinType (SEQUENCE s)          = do d <- prettySeq'' s
                                             return $ text "SEQUENCE" <> space <> braces d
prettyBuiltinType (SET s)               = do d <- prettySeq s
                                             return $ text "SET" <> space <> braces d
prettyBuiltinType (SEQUENCEOF t)        = do d <- prettySeqOfType t
                                             return $ text "SEQUENCE OF" <+> d
prettyBuiltinType (SETOF t)             = do d <- prettySeqOfType t

                                             return $ text "SET OF" <+> d
prettyBuiltinType OCTETSTRING           = return $ text "OCTETSTRING"
prettyBuiltinType (BITSTRING namedBits) = return $ text "BITSTRING" <+> braces (text "FIXME: the named bits")
prettyBuiltinType VISIBLESTRING         = return $ text "VISIBLESTRING"
prettyBuiltinType NUMERICSTRING         = return $ text "NUMERICSTRING"
prettyBuiltinType UNIVERSALSTRING       = return $ text "UNIVERSALSTRING"
prettyBuiltinType BMPSTRING             = return $ text "BMPSTRING"
prettyBuiltinType NULL                  = return $ text "NULL"
prettyBuiltinType (ENUMERATED enums)    = return $ text "ENUMERATED" <+> braces (text "FIXME: the enumeratees")
-- FIXME: For now ignore the tag information
prettyBuiltinType (TAGGED _tagInfo t)   = do u <- prettyType t
                                             error $ render u

prettySeqOfType :: SeqSetOf c => c a -> ASNPrettyM Doc
prettySeqOfType t 
		= let (f,s) = splitName t
		  in
			case f of
			     Nothing -> do prettyType s
			     Just n  -> do prettyNamedType (NamedType n s)


prettyReferencedType :: TypeReference -> ASNType a -> ASNPrettyM Doc
prettyReferencedType r t = do
  refTypes <- get
  let x = Map.lookup r refTypes
  case x of
     Nothing -> do
        d <- prettyType t
        let refTypes' = Map.insert r d refTypes
        put refTypes'
     Just _ -> do
        return ()
  return $ text (ref r)



prettyPlicity Implicit = text "IMPLICIT"
prettyPlicity Explicit = text "EXPLICIT"

prettyElementSetSpecs :: ASNType a -> SubtypeConstraint a -> ASNPrettyM Doc
prettyElementSetSpecs t (RootOnly c)              = prettyConstraint t c
prettyElementSetSpecs t (EmptyExtension c)        = do d <- prettyConstraint t c
                                                       return $ d <> comma <+> text "..."
prettyElementSetSpecs t (NonEmptyExtension c1 c2) = do d1 <- prettyConstraint t c1
                                                       d2 <- prettyConstraint t c2
                                                       return $ d1 <> comma <+> text "..." <> comma <+> d2


prettyConstraint :: ASNType a -> ElementSetSpec a -> ASNPrettyM Doc
prettyConstraint t (UnionSet u)      = prettyUnion t u
prettyConstraint t (ComplementSet e) = prettyExcept t e

prettyExcept :: ASNType a -> Exclusions a -> ASNPrettyM Doc
prettyExcept t (EXCEPT e) = prettyElem t e

prettyUnion :: ASNType a -> Unions a -> ASNPrettyM Doc
prettyUnion t (NoUnion ic)    = prettyIntersectionConstraint t ic
prettyUnion t (UnionMark u i) = do d1 <- prettyUnion t u
                                   d2 <- prettyIntersectionConstraint t i
                                   return $ d1 <+> text "|" <+> d2


prettyIntersectionConstraint :: ASNType a -> Intersections a -> ASNPrettyM Doc
prettyIntersectionConstraint t (NoIntersection ie)      = prettyInterSectionElement t ie
prettyIntersectionConstraint t (IntersectionMark ic ie) = do d1 <- prettyIntersectionConstraint t ic
                                                             d2 <- prettyInterSectionElement t ie
                                                             return $ d1 <+> text "^" <+> d2

prettyInterSectionElement t (ElementConstraint e)       = prettyElem t e
prettyInterSectionElement t (ExclusionConstraint e exc) = do d1 <- prettyElem t e
                                                             d2 <- prettyExclusion t exc
                                                             return $ d1 <+> text "EXCEPT" <+> d2

prettyExclusion :: ASNType a -> Exclusions a -> ASNPrettyM Doc
prettyExclusion t (EXCEPT e) = prettyElem t e

prettyElem :: ASNType a -> Element a -> ASNPrettyM Doc
prettyElem t (S s)  = prettySingleValue t s
prettyElem t (V r)  = prettyValueRange t r
prettyElem t (P a)  = prettyPermittedAlphabet t a
prettyElem t (C c)  = error "C"
prettyElem t (SZ s) = prettySizedElem t s
prettyElem t (IT i) = error "IT"

prettySizedElem :: ASNType a -> SizeConstraint a -> ASNPrettyM Doc
prettySizedElem t (SC x) = do d <- prettyElementSetSpecs (BuiltinType INTEGER) x
                              return $ text "SIZE" <+> parens d

prettyPermittedAlphabet :: ASNType a -> PermittedAlphabetConstraint a -> ASNPrettyM Doc
prettyPermittedAlphabet t (FR a) = do d <- prettyElementSetSpecs t a
                                      return $ text "FROM" <+> parens d

prettyValueRange :: ASNType a -> ValueRangeConstraint a -> ASNPrettyM Doc
prettyValueRange (BuiltinType INTEGER) (R (x,y))         = return $ pretty x <> text ".." <> pretty y
prettyValueRange (BuiltinType IA5STRING) (R (x,y))       = return $ text (iA5String x) <> text ".." <> text (iA5String y)
prettyValueRange (BuiltinType PRINTABLESTRING) (R (x,y)) = return $ text (printableString x) <> text ".." <> text (printableString y)
prettyValueRange (BuiltinType NUMERICSTRING) (R (x,y))   = return $ text (numericString x) <> text ".." <> text (numericString y)
prettyValueRange (BuiltinType (BITSTRING _)) (R (x,y))   = return $ text (show x) <> text ".." <> text (show y)

-- FIXME: Everything below is temporary
prettyValueRange (ReferencedType _ _) _          = return $ text "FIXME: prettyValueRange ReferencedType"
prettyValueRange (ConstrainedType _ _) _         = return $ text "FIXME: prettyValueRange ConstrainedType"
prettyValueRange (BuiltinType BOOLEAN) _         = return $ text "FIXME: prettyValueRange BuiltinType BOOLEAN"
prettyValueRange (BuiltinType (ENUMERATED _)) _  = return $ text "FIXME: prettyValueRange BuiltinType ENUMERATED"
prettyValueRange (BuiltinType OCTETSTRING) _     = return $ text "FIXME: prettyValueRange BuiltinType OCTETSTRING"
prettyValueRange (BuiltinType VISIBLESTRING) (R (x, y)) = return $ doubleQuotes (text $ visibleString x) <>
                                                                   text ".." <>
                                                                   doubleQuotes (text $ visibleString y)
prettyValueRange (BuiltinType UNIVERSALSTRING) _ = return $ text "FIXME: prettyValueRange BuiltinType UNIVERSALSTRING"
prettyValueRange (BuiltinType BMPSTRING) _       = return $ text "FIXME: prettyValueRange BuiltinType BMPSTRING"
prettyValueRange (BuiltinType NULL) _            = return $ text "FIXME: prettyValueRange BuiltinType NULL"
prettyValueRange (BuiltinType (SEQUENCE _)) _    = return $ text "FIXME: prettyValueRange BuiltinType SEQUENCE"
prettyValueRange (BuiltinType (SEQUENCEOF _)) _  = return $ text "FIXME: prettyValueRange BuiltinType SEQUENCEOF"
prettyValueRange (BuiltinType (SET _)) _         = return $ text "FIXME: prettyValueRange BuiltinType SET"
prettyValueRange (BuiltinType (SETOF _)) _       = return $ text "FIXME: prettyValueRange BuiltinType SETOF"
prettyValueRange (BuiltinType (CHOICE _)) _      = return $ text "FIXME: prettyValueRange BuiltinType CHOICE"
prettyValueRange (BuiltinType (TAGGED _ _)) _    = return $ text "FIXME: prettyValueRange BuiltinType TAGGED"



prettySingleValue :: ASNType a -> SingleValueConstraint a -> ASNPrettyM Doc
prettySingleValue (BuiltinType INTEGER) (SV e)         = return $ text (show e)
prettySingleValue (BuiltinType (BITSTRING _)) (SV e)   = return $ prettyBitString e
prettySingleValue (BuiltinType IA5STRING) (SV e)       = return $ text (show e)
prettySingleValue (BuiltinType PRINTABLESTRING) (SV e) = return $ doubleQuotes (text (printableString e))

-- FIXME: Everything below is temporary
prettySingleValue (ReferencedType _ _) _          = return $ text "FIXME: prettySingleValue ReferencedType"
prettySingleValue (ConstrainedType _ _) _         = return $ text "FIXME: prettySingleValue ConstrainedType"
prettySingleValue (BuiltinType BOOLEAN) _         = return $ text "FIXME: prettySingleValue BOOLEAN"
prettySingleValue (BuiltinType (ENUMERATED _)) _  = return $ text "FIXME: prettySingleValue ENUMERATED"
prettySingleValue (BuiltinType OCTETSTRING) _     = return $ text "FIXME: prettySingleValue OCTETSTRING"
prettySingleValue (BuiltinType VISIBLESTRING) (SV x) = return $ text $ show $ visibleString x
prettySingleValue (BuiltinType NUMERICSTRING) _   = return $ text "FIXME: prettySingleValue NUMERICSTRING"
prettySingleValue (BuiltinType UNIVERSALSTRING) _ = return $ text "FIXME: prettySingleValue UNIVERSALSTRING"
prettySingleValue (BuiltinType BMPSTRING) _       = return $ text "FIXME: prettySingleValue BMPSTRING"
prettySingleValue (BuiltinType NULL) _            = return $ text "FIXME: prettySingleValue NULL"
prettySingleValue (BuiltinType (SEQUENCE _)) _    = return $ text "FIXME: prettySingleValue SEQUENCE"
prettySingleValue (BuiltinType (SEQUENCEOF _)) _  = return $ text "FIXME: prettySingleValue SEQUENCEOF"
prettySingleValue (BuiltinType (SET _)) _         = return $ text "FIXME: prettySingleValue SET"
prettySingleValue (BuiltinType (SETOF _)) _       = return $ text "FIXME: prettySingleValue SETOF"
prettySingleValue (BuiltinType (CHOICE _)) _      = return $ text "FIXME: prettySingleValue CHOICE"
prettySingleValue (BuiltinType (TAGGED _ _)) _    = return $ text "FIXME: prettySingleValue TAGGED"


prettyBitString = (<> text "B") . (quotes . text . concat . map show .  bitString)

class Pretty a where
   pretty :: a -> Doc

instance Pretty InfInteger where
   pretty NegInf = text "MIN"
   pretty PosInf = text "MAX"
   pretty (Val x)  = text (show x)

prettyTypeVal :: ASNType a -> a -> Doc
prettyTypeVal (BuiltinType INTEGER) x = pretty x
prettyTypeVal (BuiltinType (SEQUENCE s)) x = error "SEQUENCE"

prettyElementTypeVal :: ComponentType a -> a -> Doc
prettyElementTypeVal (MandatoryComponent (NamedType n t)) x =
   text n <+> prettyTypeVal t x




