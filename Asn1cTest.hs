module Asn1cTest where

import Text.PrettyPrint
import Data.Char
import ConstrainedType
import Pretty
import qualified Data.Set as S
import Data.Word
import Data.List

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
            topLevelNamedTypeValC nt v, -- sequenceC cPtr ntSeq v,
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

elemC :: Doc -> ElementType a -> a -> Doc
elemC prefix (ETMandatory (NamedType n _ t)) x =
   typeValC (prefix <> text n) t x

typeValC :: Doc -> ASNType a -> a -> Doc
typeValC prefix a@(BITSTRING []) x = bitStringC prefix a x
typeValC prefix a@INTEGER x        = prefix <> text " = " <> text (show x) <> semi
typeValC prefix a@(RANGE t l u) x  = typeValC prefix t x
typeValC prefix a@(SIZE t s e) x   = typeValC prefix t x
typeValC prefix a@(SEQUENCE s) x   = sequenceC prefix s x

namedTypeValC :: Doc -> NamedType a -> a -> Doc
namedTypeValC prefix nt@(NamedType name tagInfo t) v =
   typeValC (prefix <+> text name) t v

topLevelNamedTypeValC :: NamedType a -> a -> Doc
topLevelNamedTypeValC nt@(NamedType name tagInfo t) v =
   typeValC (parens (text "*" <> text (lowerFirst name))) t v

type7       = NamedType "T3" Nothing (SEQUENCE (Cons (ETMandatory type7First) (Cons (ETMandatory type7Second) (Cons (ETMandatory type7Nest1) Nil))))
type7First  = NamedType "first" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Second = NamedType "second" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest1   = NamedType "nest1" Nothing (SEQUENCE (Cons (ETMandatory type7Fifth) (Cons (ETMandatory type7Fourth) (Cons (ETMandatory type7Nest2) Nil))))
type7Third  = NamedType "third" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Fourth = NamedType "fourth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

type7Nest2  = NamedType "nest2" Nothing (SEQUENCE (Cons (ETMandatory type7Fifth) (Cons (ETMandatory type7Sixth) Nil)))
type7Fifth  = NamedType "fifth" Nothing (RANGE INTEGER (Just 0) (Just 65535))
type7Sixth  = NamedType "sixth" Nothing (RANGE INTEGER (Just 0) (Just 65535))

val7 = (3:*:( 5:*:((7:*:(11:*:((13:*:(17:*:Empty)):*:Empty))):*:Empty)))

type8       = NamedType "T4" Nothing (SEQUENCE (Cons (ETMandatory type8First) (Cons (ETMandatory type8Second) (Cons (ETMandatory type8Nest1) Nil))))
type8First  = NamedType "first"  Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)
type8Second = NamedType "second" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)

type8Nest1  = NamedType "nest1"  Nothing (SEQUENCE (Cons (ETMandatory type8Third) (Cons (ETMandatory type8Fourth) Nil)))
type8Third  = NamedType "third"  Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)
type8Fourth = NamedType "fourth" Nothing (SIZE (BITSTRING []) (Elem (S.fromList [0..65537])) NoMarker)

val8 = ((BitString (bs8 12)):*:((BitString (bs8 20)):*:(((BitString (bs8 36)):*:((BitString (bs8 52)):*:Empty)):*:Empty)))

bs8 n = take n (cycle [1,0,1,0,0,0,0,0])

{-
  T5 ::=
    SEQUENCE {
      first INTEGER (0..65535),
      second BIT STRING (SIZE (0..65537))
    }
-}

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