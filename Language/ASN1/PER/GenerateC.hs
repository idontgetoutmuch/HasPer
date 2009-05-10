{-# OPTIONS_GHC -fwarn-unused-imports -fwarn-incomplete-patterns
                -XScopedTypeVariables
#-}

-----------------------------------------------------------------------------
-- |
-- Module      : Language.ASN1.PER.GenerateC
-- Copyright   : Dominic Steinitz
-- License     : BSD3-style (see LICENSE)
--
-- Maintainer  : Dominic Steinitz <dominic.steinitz@blueyonder.co.uk>
-- Stability   : experimental
--
-- TBD
-----------------------------------------------------------------------------

module Language.ASN1.PER.GenerateC
   (
     generateC
   , generateCRead
   ) where

import Text.PrettyPrint
import Data.Char
import Data.Time

import ASNTYPE
import NewTestData -- FIXME: Temporary - tests should not be done in the module
import NewPretty

-- | Generate a C program which writes out PER to a file given an ASN.1 type
-- and a corresponding value.
generateC :: ASNType a -> a -> IO Doc
generateC t x =
   do zt <- getZonedTime       
      return (creationData zt $$ includeFiles t $$ fileFunction $$ mainC t x)

-- | Generate a C program which reads PER from a file given an ASN.1 type
-- and a corresponding value.
generateCRead :: ASNType a -> a -> IO Doc
generateCRead t x =
   do zt <- getZonedTime       
      return (creationData zt $$ includeFiles t $$ mainCRead t x)

cComment :: Doc -> Doc
cComment x = text "/*" <+> x <+> text "*/"

cCommentBlock :: [Doc] -> Doc
cCommentBlock = undefined

cStatement :: Doc -> Doc
cStatement x = x <> semi

myBraces x = foldr ($+$) empty [text "{", nest 2 x, text "}"]

nestLevel = 2

cIf :: Doc -> [Doc] -> Doc
cIf condition statements =
   text "if (" <> condition <> text ")" $+$  nest 2 (myBraces (vcat statements))

cIfElse :: Doc -> [Doc] -> [Doc] -> Doc
cIfElse condition ts fs =
   text "if (" <> condition <> text ")" $+$ 
   nest 2 (myBraces (vcat ts)) $+$
   text "else" $+$
   nest 2 (myBraces (vcat fs))

cMainFunction :: Doc -> Doc
cMainFunction x = foldr ($+$) empty
                              [ text "int main(int ac, char **av) {"
                              , space
                              , nest nestLevel x
                              , text "}\n"
                              ]

mainCRead :: ASNType a -> a -> Doc
mainCRead t@(ReferencedType r ct) v =
   cMainFunction (readBody t)

readBody t@(ReferencedType r ct) = 
   foldr ($+$) empty ss
   where
      ss =
         [ cStatement (text "char buf[1024]") <+> cComment (text "Temporary buffer")
         , cStatement (cType <+> text "*" <> cPtr <+> text "= 0") <+> cComment (text "Type to decode")
         , cStatement (text "asn_dec_rval_t rval") <+> cComment (text "Decoder return value")
         , cStatement (text "FILE *fp") <+> cComment (text "Input file handler")
         , cStatement (text "size_t size") <+> cComment (text "Number of bytes read")
         , cStatement (text "char *filename") <+> cComment (text "Input file name")
         , space
         , cComment (text "Require a single filename argument")
         , cIfElse (text "ac != 2")
                   [
                     cStatement (text "fprintf(stderr, \"Usage: %s <file.per>\\n\", av[0])")
                   , cStatement (text "exit(64)") <+> cComment (text "better, EX_USAGE")
                   ]
                   [
                     cStatement (text "filename = av[1]")
                   ]
         , space
         , readFileFunction
         , space
         , cComment (text "Decode the input buffer as" <+> text name <+> text "type")
         , cStatement (text "rval = uper_decode(0, &asn_DEF_" <> text name <> comma <+>
                       text "(void **)&" <> cPtr <> comma <+> text "buf, size, 0, 0)")
         , cIf (text "rval.code != RC_OK")
               [ cStatement (text "fprintf(stderr," $+$
                              nest nestLevel (text "\"%s: Broken" <+> text name <+>
                                              text "encoding at byte %ld\\n\"" <> comma $+$
                                              text "filename" <> comma <+> text "(long)rval.consumed)"))
               , cStatement (text "exit(65)") <+> cComment (text "better, EX_DATAERR")
               ]
         , space
         , cComment (text "Print the decoded" <+> text name <+> text "type as XML")
         , cStatement (text "xer_fprint(stdout, &asn_DEF_" <> text name <> comma <+> cPtr <> text ")")
         , space
         , cStatement (text "return 0") <+> cComment (text "Decoding finished successfully")
         ]
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"
      name = ref r

mainC :: ASNType a -> a -> Doc
mainC t@(ReferencedType r ct) v = 
   foldr ($+$) empty [
        text "int main(int ac, char **av) {"
      , nest 2 (
           vcat [
                space
              , cComment (text "Declare a pointer to a" <+> text name <+> text "type")
              , cType <+> text "*" <> cPtr <> semi
              , space
              , cComment (text "Encoder return value")
              , text "asn_enc_rval_t ec;"
              , space
              , cComment (text "Allocate an instance of " <+> text name)
              , cPtr <> text " = calloc(1, sizeof(" <> cType <> text "));" <+> cComment (text "not malloc!")
              , text "assert(" <> cPtr <> text ");" <+> cComment(text "Assume infinite memory")
              , space
              , cComment (text "Initialize" <+> text name)
              , referenceTypeAndVal t v
              , space
              , text "if(ac < 2) {"
              , nest 5 (text "fprintf(stderr,\"Specify filename for PER output\\n\");")
              , text "} else {"
              , nest 5 (
                     vcat [
                          text "const char *filename = av[1];"
                        , text "FILE *fp = fopen(filename,\"wb\");    /* for PER output */"
                        , text "if(!fp) {"
                        , nest 5 (
                             vcat [
                                  text "perror(filename);"
                                , text "exit(71); /* better, EX_OSERR */"
                                  ]
                          )
                     , text "}"
                     , text "/* Encode " <> text name <> text " as PER */"
                     , text "ec = uper_encode(&asn_DEF_" <> text name <> text "," <> cPtr <> text ",write_out,fp);"
                     , text "fclose(fp);"
                     , text "if(ec.encoded == -1) {"
                     , nest 5 (
                         vcat [
                              text "fprintf(stderr,\"Could not encode " <> text name <> text " (at %s)\\n\","
                            , text "ec.failed_type ? ec.failed_type->name : \"unknown\");"
                          ]
                       )
                     , text "exit(65); /* better, EX_DATAERR */"
                     , text "} else {"
                     , text "fprintf(stderr,\"Created %s with PER encoded " <> text name <> text "\\n\",filename);"
                     , text "}"
                    ]
                )
              , text "}"
              , text "/* Also print the constructed " <> text name <> text " XER encoded (XML) */"
              , text "xer_fprint(stdout,&asn_DEF_" <> text name <> text "," <> cPtr <> text ");"
              , text "return 0; /* Encoding finished successfully */"
              ]
           )
      , text "}\n"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"
      name = ref r

-- | Display date and time of file creation
creationData :: ZonedTime -> Doc
creationData zt =
   text "/*" $$
   text "*" $$
   text "* Created by the Haskell ASN.1 Test Framework" <+> text (show zt) $$
   text "*" $$
   text "*/" $$
   space

-- | Include the relevant .h files
includeFiles :: ASNType a -> Doc
includeFiles (ReferencedType r _) =
   text "#include <stdio.h>   /* for stdout */" $$
   text "#include  <stdlib.h> /* for malloc () */" $$
   text "#include  <assert.h> /* for run-time control */" $$
   text "#include \"" <> text name <> text ".h\"" <> space <> text "/* " <> text name <> text " ASN.1 type */" $$
   space
   where
      name = ref r

-- | A function to write to file.
fileFunction = 
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

-- | Code to read from a file. FIXME: Should this be a C function
-- since the write equivalent is? Let's pretend it generates a C
-- function for now by calling it 'readFileFunction' rather than
-- \'readFileCode\'.
readFileFunction =
   vcat [ cComment   (text "Open input file as read-only binary")
        , cStatement (text "fp = fopen(filename,\"rb\")")
        , cIf (text "!fp") [ cStatement (text "perror(filename)")
                           , cStatement (text "exit(66)") <+>
                                         cComment (text "better, EX_NOINPUT")
                           ]
        , space
        , cComment   (text "Read up to the buffer size")
        , cStatement (text "size = fread(buf, 1, sizeof(buf), fp)")
        , cStatement (text "fclose(fp)")
        , cIf (text "!size") [ cStatement (text "fprintf(stderr, \"%s: Empty or broken\\n\", filename)")
                             , cStatement (text "exit(65)") <+>
                                           cComment (text "better, EX_DATAERR")
                             ]
        ]

-- | Allocate memory for a variable
allocPointer :: String -> Doc
allocPointer name =
   foldr ($+$) empty [
      text "/* Allocate an instance of " <+> text name <+> text "*/",
      cPtr <> text " = calloc(1, sizeof(" <> cType <> text ")); /* not malloc! */",
      text "assert(" <> cPtr <> text "); /* Assume infinite memory */"
      ]
   where
      cPtr = text (lowerFirst name)
      cType = text name <> text "_t"

lowerFirst :: String -> String
lowerFirst "" = ""
lowerFirst (x:xs) = (toLower x):xs

referenceTypeAndVal :: ASNType a -> a -> Doc
referenceTypeAndVal (ReferencedType r t) v =
   referenceTypeAndValAux1 [(ref r)] t v 
referenceTypeAndVal (ConstrainedType _ _) _ =
   error "I don't know how to create C for a ConstrainedType"
referenceTypeAndVal (BuiltinType b) v =
   error "I don't know how to create C for a BuiltinType"

referenceTypeAndValAux1 :: Prefix -> ASNType a -> a -> Doc
referenceTypeAndValAux1 ns (BuiltinType b) v =
   referenceTypeAndValAux2 ns b v

referenceTypeAndValAux2 :: Prefix -> ASNBuiltin a -> a -> Doc
referenceTypeAndValAux2 ns INTEGER      x = lhs ns <> text " = " <> prettyTypeVal (BuiltinType INTEGER) x <> semi
referenceTypeAndValAux2 ns (SEQUENCE s) x = cSEQUENCE ns s x

cSEQUENCE :: Prefix -> Sequence a -> a -> Doc
cSEQUENCE _ EmptySequence _ = 
   empty
cSEQUENCE ns (AddComponent t ts) (x:*:xs) =
   cComponent (".":ns) t x $$
   cSEQUENCE ns ts xs

cComponent :: Prefix -> ComponentType a -> a -> Doc
cComponent ns (MandatoryComponent (NamedType n t)) x =
   referenceTypeAndValAux1 (n:ns) t x

type Prefix = [Name]

lhs :: Prefix -> Doc
lhs ns = 
   pointer <> components
   where
      (x:xs) = reverse ns
      pointer = parens (text "*" <> text (lowerFirst x))
      components = hcat (map text xs)


eg1 = referenceTypeAndVal (ReferencedType (Ref "MyType") (BuiltinType INTEGER)) (Val 3)

eg2 = 
   referenceTypeAndVal
      (ReferencedType (Ref "Type2") (BuiltinType (SEQUENCE (AddComponent mc2 (AddComponent mc1 EmptySequence)))))
      ((Val 5) :*: ((Val 3) :*: Empty))      
   where 
      mc1 = MandatoryComponent (NamedType "component1" (BuiltinType INTEGER))
      mc2 = MandatoryComponent (NamedType "component2" (BuiltinType INTEGER))

eg3 = 
   referenceTypeAndVal rt3 y
   where
      x   = (Val 5) :*: ((Val 3) :*: Empty)
      y   = x :*: ( x :*: Empty)

x3 = (Val 5) :*: ((Val 3) :*: Empty)
y3 = x3 :*: ( x3 :*: Empty)
