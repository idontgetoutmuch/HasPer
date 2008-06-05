import Text.PrettyPrint

data ZeroTuple = ZeroTuple
data Tuple e es = Tuple e es

newtype IA5String = IA5String {unIA5String :: String}

-- A cut down representation for ASN.1 types.

data ASNType :: * -> * where
   BOOLEAN   :: ASNType Bool
   INTEGER   :: ASNType Integer
   IA5STRING :: ASNType IA5String
   SEQUENCE  :: Sequence a -> ASNType a

data Sequence :: * -> * where
   NilSeq     :: Sequence ZeroTuple
   ConsSeq    :: ASNType a -> Sequence l -> Sequence (Tuple a l)

prettyType :: ASNType a -> Doc
prettyType BOOLEAN   = text "BOOLEAN"
prettyType INTEGER   = text "INTEGER"
prettyType IA5STRING = text "IA5STRING"

type FieldName = String

-- Object class components

data ObjClassComponent :: * -> * where
   OCType                 :: FieldName -> ObjClassComponent a
   OCFixedTypeValue       :: FieldName -> ASNType a -> ObjClassComponent a
   OCVariableTypeValue    :: FieldName -> ObjClassComponent a -> ObjClassComponent a
   OCFixedTypeValueSet    :: FieldName -> ASNType a -> ObjClassComponent a
   OCVariableTypeValueSet :: FieldName -> ObjClassComponent a -> ObjClassComponent a
   OCInformationObject    :: FieldName -> ObjClass a -> ObjClassComponent a

-- And object classes themselves

data ObjClass :: * -> * where
   Singleton :: ObjClassComponent a -> ObjClass a
   Cons      :: ObjClassComponent a -> ObjClass l -> ObjClass (Tuple a l)
   Lift      :: Mu a l -> ObjClass (Mu a l)

-- We need recursive types because in ASN.1 an object class can refer to itself.

data Mu :: * -> * -> * where
   Inl :: ObjClass (Tuple (Mu a b) b) -> Mu a b
   Inr :: ObjClass (Tuple a (Mu a b)) -> Mu a b

{-

The definition in Haskell below is very similar to the one on page 314 in
Dubuisson which is reproduced below.

OTHER-FUNCTION ::= CLASS {
  &code                INTEGER (0..MAX) UNIQUE,
  &Alphabet            BMPString
    DEFAULT {Latin1 INTERSECTION Level1},
  &ArgumentType        ,
  &SupportedArguments &ArgumentType OPTIONAL,
  &ResultType          DEFAULT NULL,
  &result-if-error     &ResultType DEFAULT NULL,
  &associated-function OTHER-FUNCTION OPTIONAL,
  &Errors              ERROR DEFAULT
    {rejected-argument | memory-fault} }

-}

x1 = OCType "ArgumentType"
x2 = OCFixedTypeValue "code" INTEGER
x3 = OCType "ResultType"
x4 = OCVariableTypeValue "result-if-error" x3
x5 = OCFixedTypeValueSet "Alphabet" IA5STRING
x6 = OCVariableTypeValueSet "Supported Arguments" x1
x7 = OCFixedTypeValueSet "Errors" BOOLEAN

x = Lift (Inr (Cons x7 (Lift (Inl (Cons (OCInformationObject "other function" x) (Cons x6 (Cons x5 (Cons x4 (Cons x3 (Cons x2 (Singleton x1)))))))))))

printObjClassComp (OCType fn) = text "Type" <+> text fn
printObjClassComp (OCFixedTypeValue fn t) = text "Fixed Type Value" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValue fn c) = text "Variable Type Value" <+> text fn <+> braces (printObjClassComp c)
printObjClassComp (OCFixedTypeValueSet fn t) = text "Fixed Type Value Set" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValueSet fn c) = text "Variable Type Value Set" <+> text fn <+> braces (printObjClassComp c)
printObjClassComp (OCInformationObject fn oc)  = text "Information Object" <+> text fn

prettyOC :: ObjClass a -> Doc
prettyOC (Singleton occ) = printObjClassComp occ
prettyOC (Cons occ oc) = printObjClassComp occ $$ prettyOC oc
prettyOC (Lift mu) = prettyMu mu

prettyMu :: Mu a b -> Doc
prettyMu (Inl oc) = prettyOC oc
prettyMu (Inr oc) = prettyOC oc

{-
A good explanation of object classes, their motivation and use.

Email to the ASN.1 mailing list from Jeffrey Walton

AlgorithmIdentifier ::= SEQUENCE {
algorithm ALGORITHM.&id ({SupportedAlgorithms}),
parameters ALGORITHM.&Type ({SupportedAlgorithms}{ @algorithm}) OPTIONAL }

[1] X.509, The Directory: Public-key and Attribute Certificate
Frameworks, http://www.itu.int/rec/T-REC-X/recommendation.asp?lang=en&parent=T-REC-X.509,
August 2008, p 11.

Response from Conrad Sigona

If you look for the definition of ALGORITHM on p. 101, you'll find

  ALGORITHM ::= TYPE-IDENTIFIER

and if you look in a textbook about ASN.1 or in the ASN.1 standard documents, you'll find

  TYPE-IDENTIFIER ::= CLASS {
     &id   OBJECT IDENTIFIER UNIQUE,
     &Type }
  WITH SYNTAX { &Type IDENTIFIED BY &id }

Thus ALGORITHM is not a type, but a CLASS. On the other hand, ALGORITHM.&id is a type, namely, an OBJECT IDENTIFIER. ALGORITHM.&Type is also a type, an open type. 
This means it can be various types, but since it is constrained by ({SupportedAlgorithms}{ @algorithm}), it is not just any type, but one that fits the constraint. 
Let's look at the two elements one at a time.

ALGORITHM.&id is, as we said above, an OBJECT IDENTIFIER. Since it appears as

  ALGORITHM.&id ({SupportedAlgorithms})

it is constrained to be one of the OBJECT IDENTIFIERs in the SupportedAlgorithms object set. Page 22 shows

  -- Definition of the following information object set
  -- is deferred, perhaps to standardized profiles or
  -- to protocol implementation conformance statements.
  -- The set is required to specify a table constraint
  -- on the parameters component of AlgorithmIdentifier.
  -- SupportedAlgorithms ALGORITHM ::= { ... }

which says that SupportedAlgorithms should be defined but isn't (yet). If it were defined, it would look something like

  SupportedAlgorithms ALGORITHM ::= {
       Algo1 IDENTIFIED BY { 1 2 3 4 1 } |
       Algo2 IDENTIFIED BY { 1 2 3 4 2 } |
       Algo3 IDENTIFIED BY { 1 2 3 4 3 },
       ...
  }

I just made up some types (Algo1, Algo2, and Algo3) and objects identifiers. They serve only as examples and have no meaning per se.

Note the "WITH SYNTAX" in the definition of TYPE-IDENTIFIER above.
It describes the way to specify each object as a type (&Type) followed by the string "IDENTIFIED BY" followed by an OBJECT IDENTIFIER (&id). 
Thus Algo1 is associated with { 1 2 3 4 1 }; Algo2 is associated with { 1 2 3 4 2 }; and Algo3 is associated with { 1 2 3 4 3 }.

I wrote above that ALGORITHM.&id is constrained to be one of the OBJECT IDENTIFIERS in the SupportedAlgorithms object set. 
Using my example above, you see that it is limited to taking the value of one of the three object identifiers.

ALGORITHM.&Type ({SupportedAlgorithms}{ @algorithm}) is an open type constrained to be one of the types specified in SupportedAlgorithms depending upon algorithm. 
Bear in mind the definition of algorithm, and you'll see that what


  AlgorithmIdentifier ::= SEQUENCE {
     algorithm ALGORITHM.&id ({SupportedAlgorithms}),
     parameters ALGORITHM.&Type
             ({SupportedAlgorithms}{ @algorithm}) OPTIONAL
   }

means is that we have a SEQUENCE consisting of

a) algorithm, which is one of the OBJECT IDENTIFIERs drawn from the set above, and

b) parameters, which is an open type also drawn from the set above, but which depends upon algorithm.

You can look at SupportedAlgorithm as a set of rules, namely,
if algorithm = { 1 2 3 4 1 }, then parameters is Algo1;
if algorithm = { 1 2 3 4 2 }, then parameters is Algo2;
if algorithm = { 1 2 3 4 3 }, then parameters is Algo3;
if algorithm is anything else (...), then parameters can be anything, that is, some type, but unspecified.

So what can you do with this information? Now you know what the syntax means, but you still need either a fully specified SupportedAlgorithms or else knowledge from some external source (e.g., a sheet of paper) that tells you which type is associated with which object identifier.

I guess you were hoping to get a simpler and more pointed answer. Unfortunately I have none. If you wish to learn more about information object classes, information object sets, and open types, permit me to suggest

   http://www.oss.com/asn1/booksintro.html

where you can download two ASN.1 reference manuals. They are both
comprehensive, although with different emphasis. Each has its own fans,
but both are quite good.

-}

y1 = OCType "Type"
y2 = OCFixedTypeValue "id" INTEGER -- for the time being since we don't bother with OIDs yet
y3 = Cons y1 (Singleton y2)

-- Should we "tuple" with ZeroTuple as well?

a1 = Tuple BOOLEAN   12341
a2 = Tuple INTEGER   12342
a3 = Tuple IA5STRING 12343

-- Object Sets aren't really sets as they are inhabited by objects of different types.
-- We can represent them as "tuples".

data ObjSet :: * -> * where
   ObjZero :: ObjSet ZeroTuple
   ObjCons :: ObjClass a -> a -> ObjSet b -> ObjSet (Tuple a b)

b1 = ObjCons y3 a1 ObjZero
b2 = ObjCons y3 a2 b1

-- Here's an example of how you could use the "library".

type ErrorMsg = String

data SupportedTypes = SupportedBool Bool | SupportedInteger Integer | Unsupported ErrorMsg
   deriving Show

h :: ObjClass (Tuple a Integer) -> (Tuple (ASNType a) Integer) -> String -> SupportedTypes
h (Cons _ (Singleton (OCFixedTypeValue _ _))) (Tuple _ 12341) s = SupportedInteger (read s)
h (Cons _ (Singleton (OCFixedTypeValue _ _))) (Tuple _ 12342) s = SupportedBool (read s)
h _                                           (Tuple _ x)     _ = Unsupported ("OID: " ++ (show x) ++ " not supported")

-- ObjSet is too general. We want to constrain only the right "shaped" ObjClass values to be added.
-- It's not clear how to do this.
