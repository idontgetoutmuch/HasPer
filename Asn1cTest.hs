module Asn1cTest where

import Text.PrettyPrint
import Data.Char
import ConstrainedType
import Pretty
import qualified Data.Set as S
import Data.Word
import Data.List
import Language.ASN1 hiding (BitString, NamedType, ComponentType)
import QuickTest (genModule', RepTypeVal(..))

genC :: NamedType a -> a -> Doc
genC nt@(NamedType name tagInfo t) v =
   text "#include <stdio.h>   /* for stdout */" $$
   text "#include  <stdlib.h> /* for malloc () */" $$
   text "#include  <assert.h> /* for run-time control */" $$
   text "#include <" <> text name <> text ".h>" <> space <> text "/* " <> text name <> text " ASN.1 type */" $$
   space $$
   preface $$
   space $$
   mainC nt v

preface = 
   vcat [
      text "/*",
      text " * This is a custom function which writes the",
      text " * encoded output into some FILE stream.",
      text " */",
      space,
      text "static int",
      text "write_out(const void *buffer, size_t size, void *app_key) {",
      nest 5 (
         vcat [
            text "FILE *out_fp = app_key;",
            text "size_t wrote;",
            text "wrote = fwrite(buffer, 1, size, out_fp);",
            text "return (wrote == size) ? 0 : -1;"
            ]
         ),
      text "}"
      ]

mainC :: NamedType a -> a -> Doc
mainC nt@(NamedType name tagInfo t) v = 
   foldr ($+$) empty [
      text "int main(int ac, char **av) {",
      nest 2 (
         vcat [
            space,
            text "/* Declare a pointer to a " <> text name <> text " type */",
            cType <+> text "*" <> cPtr <> semi,
            space,
            text "/* Encoder return value */",
            text "asn_enc_rval_t ec;",
            space,
            text "/* Allocate an instance of " <+> text name <+> text "*/",
            cPtr <> text " = calloc(1, sizeof(" <> cType <> text ")); /* not malloc! */",
            text "assert(" <> cPtr <> text "); /* Assume infinite memory */",
            space,
            text "/* Initialize" <+> text name <+> text "*/",
            newTopLevelNamedTypeValC nt v, -- sequenceC cPtr ntSeq v,
            space,
            text "if(ac < 2) {",
            nest 5 (text "fprintf(stderr,\"Specify filename for PER output\\n\");"),
            text "} else {",
            nest 5 (
               vcat [
                  text "const char *filename = av[1];",
                  text "FILE *fp = fopen(filename,\"wb\");    /* for PER output */",
                  text "if(!fp) {",
                  nest 5 (
                     vcat [
                        text "perror(filename);",
                        text "exit(71); /* better, EX_OSERR */"
                        ]
                     ),
                  text "}",
                  text "/* Encode " <> text name <> text " as PER */",
                  text "ec = uper_encode(&asn_DEF_" <> text name <> text "," <> cPtr <> text ",write_out,fp);",
                  text "fclose(fp);",
                  text "if(ec.encoded == -1) {",
                  nest 5 (
                     vcat [
                        text "fprintf(stderr,\"Could not encode " <> text name <> text " (at %s)\\n\",",
                        text "ec.failed_type ? ec.failed_type->name : \"unknown\");"
                        ]
                     ),
                  text "exit(65); /* better, EX_DATAERR */",
                  text "} else {",
                  text "fprintf(stderr,\"Created %s with PER encoded " <> text name <> text "\\n\",filename);",
                  text "}"
                  ]
               ),
               text "}",
               text "/* Also print the constructed " <> text name <> text " XER encoded (XML) */",
               text "xer_fprint(stdout,&asn_DEF_" <> text name <> text "," <> cPtr <> text ");",
               text "return 0; /* Encoding finished successfully */"
            ]
         ),
         text "}\n"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"
      (NamedType _ _ ntType) = nt
      (SEQUENCE ntSeq) = ntType

lowerFirst :: String -> String
lowerFirst "" = ""
lowerFirst (x:xs) = (toLower x):xs

callocPreamble :: String -> Doc
callocPreamble name =
   foldr ($+$) empty [
      text "/* Allocate an instance of " <+> text name <+> text "*/",
      cPtr <> text " = calloc(1, sizeof(" <> cType <> text ")); /* not malloc! */",
      text "assert(" <> cPtr <> text "); /* Assume infinite memory */"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"

sequenceC :: Doc -> Sequence a -> a -> Doc
sequenceC prefix Nil _ = empty
sequenceC prefix (Cons t ts) (x:*:xs) =
   elemC (prefix <> text ".") t x $$ 
   sequenceC prefix ts xs

newSequence :: [Name] -> Sequence a -> a -> Doc
newSequence _ Nil _ = empty
newSequence ns (Cons t ts) (x:*:xs) =
   newElementType (".":ns) t x $$
   newSequence ns ts xs

newElementType :: [Name] -> ComponentType a -> a -> Doc
newElementType ns (CTMandatory (NamedType n _ t)) x =
   newTypeValC (n:ns) t x

choiceC :: Doc -> Choice a -> HL a (S Z) -> Doc
choiceC _ NoChoice _ = empty
choiceC prefix (ChoiceOption nt cts) (NoValueC _ v) =
   choiceC prefix cts v
choiceC prefix (ChoiceOption nt cts) (ValueC v _) =
   namedTypeValC (prefix <> text ".choice.") nt v

choiceCAux :: [Name] -> Doc -> Choice a -> HL a (S Z) -> (Doc,[Name])
choiceCAux ds _ NoChoice _ = (empty,ds)
choiceCAux ds prefix (ChoiceOption _ cts) (NoValueC _ v) =
   choiceCAux ds prefix cts v
choiceCAux ds prefix (ChoiceOption nt@(NamedType n _ _) cts) (ValueC v _) =
   (namedTypeValC (prefix <> text ".choice.") nt v, n:ds)

choiceC' :: Doc -> Choice a -> HL a (S Z) -> Doc
choiceC' prefix t v = let (p,qs) = choiceCAux [] prefix t v in vcat (map text qs) $$ p

newChoice :: [Name] -> Choice a -> HL a (S Z) -> Doc
newChoice ns NoChoice _ = empty
newChoice ns (ChoiceOption _ cts) (NoValueC _ v) =
   newChoice ns cts v
newChoice ns (ChoiceOption nt@(NamedType n _ ct) cts) (ValueC v _) =
   tags ns $$
   newTypeValC (n:".choice.":ns) ct v
   where
      tags [] = empty
      tags ns = lhs ns {- hcat (map text ms) -} <> text ".present = " <> text (head ns) <> text "_PR_" <> text n <> semi
      ms = reverse ns

elemC :: Doc -> ComponentType a -> a -> Doc
elemC prefix (CTMandatory (NamedType n _ t)) x =
   typeValC (prefix <> text n) t x

typeValC :: Doc -> ASNType a -> a -> Doc
typeValC prefix a@(BITSTRING []) x = bitStringC prefix a x
typeValC prefix a@INTEGER x        = prefix <> text " = " <> text (show x) <> semi
typeValC prefix a@(RANGE t l u) x  = typeValC prefix t x
typeValC prefix a@(SIZE t s e) x   = typeValC prefix t x
typeValC prefix a@(SEQUENCE s) x   = sequenceC prefix s x
typeValC prefix a@(CHOICE c) x = choiceC' prefix c x

newTypeValC :: [Name] -> ASNType a -> a -> Doc
newTypeValC ns a@INTEGER x        = lhs ns {- hcat (map text (reverse ns)) -} <> text " = " <> text (show x) <> semi
newTypeValC ns a@(CHOICE c) x     = newChoice ns c x
newTypeValC ns a@(SEQUENCE s) x   = newSequence ns s x
newTypeValC ns a@(RANGE t l u) x  = newTypeValC ns t x
newTypeValC ns a@(SIZE t s e) x   = newTypeValC ns t x
newTypeValC ns a@(BITSTRING []) x = newBitStringC ns a x
newTypeValC _ a _ = prettyType a

lhs :: Prefix -> Doc
lhs ns = 
   pointer <> components
   where
      (x:xs) = reverse ns
      pointer = parens (text "*" <> text (lowerFirst x))
      components = hcat (map text xs)

namedTypeValC :: Doc -> NamedType a -> a -> Doc
namedTypeValC prefix nt@(NamedType name tagInfo t) v =
   typeValC (prefix <> text name) t v

topLevelNamedTypeValC :: NamedType a -> a -> Doc
topLevelNamedTypeValC nt@(NamedType name tagInfo t) v =
   typeValC (parens (text "*" <> text (lowerFirst name))) t v

newTopLevelNamedTypeValC :: NamedType a -> a -> Doc
newTopLevelNamedTypeValC nt@(NamedType name tagInfo t) v =
   newTypeValC {- [render (parens (text "*" <> text (lowerFirst name)))] -} [name] t v

oldQuickC =
   do rs <- genModule'
      let as = map g rs
          ds = map f rs
      return (vcat as $$ vcat ds)
   where
      f r =
         case r of
            RepTypeVal t v ->
               topLevelNamedTypeValC (NamedType "Foo" Nothing t) v
      g r =
         case r of
            RepTypeVal t v ->
               prettyTypeVal t v

quickC =
   do rs <- genModule'
      let as = map g rs
          ds = map f rs
      return (vcat as $$ vcat ds)
   where
      f r =
         case r of
            RepTypeVal t v ->
               newTopLevelNamedTypeValC (NamedType "Foo" Nothing t) v
      g r =
         case r of
            RepTypeVal t v ->
               prettyTypeVal t v

type7       = NamedType "T3" Nothing (SEQUENCE (Cons (CTMandatory type7First) (Cons (CTMandatory type7Second) (Cons (CTMandatory type7Nest1) Nil))))
type7First  = NamedType "first" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Second = NamedType "second" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Fourth) (Cons (CTMandatory type7Nest2) Nil))))
type7Third  = NamedType "third" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Fourth = NamedType "fourth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (CTMandatory type7Fifth) (Cons (CTMandatory type7Sixth) Nil)))
type7Fifth  = NamedType "fifth" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Sixth  = NamedType "sixth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

val7 = (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty)))

type8       = NamedType "T4" Nothing (SEQUENCE (Cons (CTMandatory type8First) (Cons (CTMandatory type8Second) (Cons (CTMandatory type8Nest1) Nil))))
type8First  = NamedType "first"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Second = NamedType "second" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

type8Nest1  = NamedType "nest1"  Nothing (SEQUENCE (Cons (CTMandatory type8Third) (Cons (CTMandatory type8Fourth) Nil)))
type8Third  = NamedType "third"  Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)
type8Fourth = NamedType "fourth" Nothing (SIZE (BITSTRING []) (Elem (0,65537)) NoMarker)

val8 = ((BitString (bs8 12)):*:((BitString (bs8 20)):*:(((BitString (bs8 36)):*:((BitString (bs8 52)):*:Empty)):*:Empty)))

bs8 n = take n (cycle [1,0,1,0,0,0,0,0])

type9 = 
   CHOICE xs
      where
         xs = ChoiceOption e1 (ChoiceOption e2 (ChoiceOption e4 NoChoice))
         e1 = NamedType "element1" (Just (Context,0,Implicit)) INTEGER
         e2 = NamedType "element2" (Just (Context,1,Explicit)) (CHOICE (ChoiceOption s1 (ChoiceOption s2 (ChoiceOption s3 NoChoice))))
         e4 = NamedType "element4" (Just (Context,2,Implicit)) INTEGER
         s1 = NamedType "subElement1" (Just (Context,3,Implicit)) INTEGER
         s2 = NamedType "subElement2" (Just (Context,4,Implicit)) INTEGER
         s3 = NamedType "subElement3" (Just (Context,5,Implicit)) INTEGER

type9' = NamedType "Type9" Nothing type9

val9 = NoValueC NoValue (ValueC (ValueC 7 (NoValueC NoValue (NoValueC NoValue EmptyHL))) (NoValueC NoValue EmptyHL))

type10 =
   CHOICE xs
      where
         xs = ChoiceOption ss1 (ChoiceOption ss2 (ChoiceOption ss3 NoChoice))
         ss1 = NamedType "superElement1" (Just (Context,6,Implicit)) INTEGER
         ss2 = NamedType "superElement2" (Just (Context,7,Explicit)) type9
         ss3 = NamedType "superElement3" (Just (Context,8,Implicit)) INTEGER

type10' = NamedType "Type10" Nothing type10

val10 = NoValueC NoValue (ValueC val9 (NoValueC NoValue EmptyHL))

type11       = NamedType "T3" Nothing (SEQUENCE (Cons (CTMandatory type11First) (Cons (CTMandatory type11Second) (Cons (CTMandatory type11Nest1) Nil))))
type11First  = NamedType "first" Nothing INTEGER 
type11Second = NamedType "second" Nothing INTEGER

type11Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (CTMandatory type11Fifth) (Cons (CTMandatory type11Fourth) (Cons (CTMandatory type11Nest2) Nil))))
type11Third  = NamedType "third" Nothing INTEGER
type11Fourth = NamedType "fourth" Nothing INTEGER

type11Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (CTMandatory type11Fifth) (Cons (CTMandatory type11Sixth) Nil)))
type11Fifth  = NamedType "fifth" Nothing INTEGER
type11Sixth  = NamedType "sixth" Nothing INTEGER

type12 =
   CHOICE xs
      where
         xs = ChoiceOption c1 (ChoiceOption c2 NoChoice)
         c1 = NamedType "c1" (Just (Context,0,Implicit)) s1
         c2 = NamedType "c2" (Just (Context,1,Implicit)) s2
         s1 = SEQUENCE (Cons (CTMandatory e1) (Cons (CTMandatory e2) Nil))
         s2 = SEQUENCE (Cons (CTMandatory e3) (Cons (CTMandatory e4) Nil))
         e1 = NamedType "one" Nothing INTEGER
         e2 = NamedType "two" Nothing INTEGER
         e3 = NamedType "three" Nothing INTEGER
         e4 = NamedType "four" Nothing INTEGER

type12' = NamedType "Type12" Nothing type12

val12a = ValueC (3:*:(4:*:Empty)) (NoValueC NoValue EmptyHL)
val12b = NoValueC NoValue (ValueC (1:*:(2:*:Empty)) EmptyHL)

bitStringC :: Doc -> ASNType a -> a -> Doc
bitStringC prefix a@(BITSTRING []) x = 
   space
   $+$
   prefix <> text ".buf = calloc(" <> text (show calloc) <> text ", 1); /* " <> text (show calloc) <> text " bytes */" 
   $$
   text "assert(" <> prefix <> text ".buf);"
   $$
   prefix <> text ".size = " <> text (show calloc) <> semi
   $$
   vcat (zipWith (<>) bufs ((map ((<> semi) . text .show) . bitStringToBytes) x))
   $$
   prefix <> text ".bits_unused = " <> text (show unusedBits) <> semi <> text " /* Trim unused bits */"
   where
      bufs = map (\x -> prefix <> text ".buf[" <> text (show x) <> text "] = ") [0..]
      (callocM1, unusedBits) = length ((bitString x)) `quotRem` 8
      calloc = callocM1 + 1

type Prefix = [Name]

newBitStringC :: Prefix -> ASNType a -> a -> Doc
newBitStringC ns a@(BITSTRING []) x =
   space
   $+$
   fns <> text ".buf = calloc (" <> text (show calloc) <> text ", 1); /* " <> text (show calloc) <> text " bytes */" 
   $$
   text "assert(" <> fns <> text ".buf);"
   $$
   fns <> text ".size = " <> text (show calloc) <> semi
   $$
   vcat (zipWith (<>) bufs ((map ((<> semi) . text .show) . bitStringToBytes) x))
   $$
   fns <> text ".bits_unused = " <> text (show unusedBits) <> semi <> text " /* Trim unused bits */"
   where
      fns = lhs ns {- hcat (map text (reverse ns)) -}
      bufs = map (\x -> fns <> text ".buf[" <> text (show x) <> text "] = ") [0..]
      (callocM1, unusedBits) = length ((bitString x)) `quotRem` 8
      calloc = callocM1 + 1

bitStringToBytes :: BitString -> [Word8]
bitStringToBytes =
   map fromNonNeg . pad . bitString

pad :: Num a => [a] -> [[a]]
pad =
   unfoldr f
      where
         f x
            | l == 0 = Nothing
            | l < 8  = Just (t ++ replicate (8 - l) 0, [])
            | otherwise = Just (t, d)
            where
               l = length t
               t = take 8 x
               d = drop 8 x

{-
main =
   writeFile "asn1c2/generated.c" (render (genC type9 val9))
-}