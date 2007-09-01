import Text.PrettyPrint
import Data.Char
import ConstrainedType

t1 = NamedType "T1" Nothing (RANGE INTEGER (Just 25) (Just 30))

t2 = NamedType "T2" Nothing (SEQUENCE (Cons (ETMandatory (NamedType "first" Nothing INTEGER)) Nil))

t3 = NamedType "T3" Nothing (SEQUENCE (
        Cons (ETMandatory (NamedType "first" Nothing INTEGER)) (
           Cons (ETMandatory (NamedType "second" Nothing INTEGER)) Nil)))

genC :: NamedType a -> a -> Doc
genC nt@(NamedType name tagInfo t) v =
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
   vcat [
      text "int main(int ac, char **av) {",
      nest 5 (
         vcat [
            cType <+> text "*" <> cPtr <> semi <+> text "/* Type to encode */",
            text "asn_enc_rval_t ec; /* Encoder return value */",
            text "/* Allocate " <+> cType <+> text "*/",
            cPtr <> text " = calloc(1, sizeof(" <> cType <> text ")); /* not malloc! */",
            text "if(!" <> cPtr <> text ") {",
            text "perror(\"calloc() failed\");",
            text "exit(71); /* better, EX_OSERR */",
            text "}",
            text "/* Initialize" <+> text name <+> text "*/",
            sequenceC cPtr ntSeq v,
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
                  text "/* Encode " <> text name <> text " as BER */",
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
                  text "fprintf(stderr,\"Created %s with BER encoded " <> text name <> text "\\n\",filename);",
                  text "}"
                  ]
               ),
               text "}",
               text "/* Also print the constructed " <> text name <> text " XER encoded (XML) */",
               text "xer_fprint(stdout,&asn_DEF_" <> text name <> text "," <> cPtr <> text ");",
               text "return 0; /* Encoding finished successfully */"
            ]
         ),
         text "}"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"
      (NamedType _ _ ntType) = nt
      (SEQUENCE ntSeq) = ntType

lowerFirst :: String -> String
lowerFirst "" = ""
lowerFirst (x:xs) = (toLower x):xs

sequenceC :: Doc -> Sequence a -> a -> Doc
sequenceC prefix Nil _ = empty
sequenceC prefix (Cons (ETMandatory (NamedType name _ t)) ts) (x:*:xs) =
   prefix <> text "->" <> text name <> text " = " <> text (show x) <> semi $$ 
   sequenceC prefix ts xs
   
