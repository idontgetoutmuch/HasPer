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

module GenerateC
   (
     allocPointer
   ) where

import Text.PrettyPrint
import Data.Char
import Data.Time

import ASNTYPE

cMain :: ASNType a -> a -> IO Doc
cMain t x =
   do zt <- getZonedTime       
      return (creationData zt $$ includeFiles t $$ fileFunction)
   

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

-- | A function to write to file
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
referenceTypeAndValAux2 ns INTEGER      x = lhs ns <> text " = " <> text (show x) <> semi
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


rt3 =
   (ReferencedType (Ref "Type3") (BuiltinType (SEQUENCE (AddComponent mc3 (AddComponent mc4 EmptySequence)))))
   where 
      mc1 = MandatoryComponent (NamedType "component1" (BuiltinType INTEGER))
      mc2 = MandatoryComponent (NamedType "component2" (BuiltinType INTEGER))
      mc3 = MandatoryComponent (NamedType "component3" s1)
      mc4 = MandatoryComponent (NamedType "component4" s1)
      s1  = BuiltinType (SEQUENCE (AddComponent mc1 (AddComponent mc2 EmptySequence)))


