import Text.PrettyPrint

data ZeroTuple = ZeroTuple
data Tuple e es = Tuple e es

newtype IA5String = IA5String {unIA5String :: String}

data ASNType :: * -> * where
   BOOLEAN   :: ASNType Bool
   INTEGER   :: ASNType Integer
   IA5STRING :: ASNType IA5String

prettyType :: ASNType a -> Doc
prettyType BOOLEAN   = text "BOOLEAN"
prettyType INTEGER   = text "INTEGER"
prettyType IA5STRING = text "IA5STRING"


data UbjClass :: * where
   USingleton :: UbjClassComponent -> UbjClass
   UCons      :: UbjClassComponent -> UbjClass -> UbjClass

type FieldName = String
   
data UbjClassComponent :: * where
   UCFTV :: FieldName -> ASNType a -> UbjClassComponent
   UCIO  :: FieldName -> UbjClass -> UbjClassComponent

uF2 = UCFTV "code" INTEGER

uF = UCons (UCIO "another" uF) (USingleton uF2)

data ObjClass :: * -> * where
   Singleton :: ObjClassComponent a -> ObjClass a
   Cons      :: ObjClassComponent a -> ObjClass l -> ObjClass (Tuple a l)
   Lift      :: Mu a l -> ObjClass (Mu a l)

data ObjClassComponent :: * -> * where
   OCFTV :: FieldName -> ASNType a -> ObjClassComponent a
   OCIO  :: FieldName -> ObjClass a -> ObjClassComponent a

oF2 = OCFTV "code" INTEGER

oF = Lift (Inl (Cons (OCIO "another" oF) (Singleton oF2)))

oFV = Inlx (Tuple oFV (3::Integer))

oG = Lift (Inr (Cons oF2 (Singleton (OCIO "another" oG))))

oH = Lift (Inl (Cons (OCIO "another" oH) (Cons oF2 (Singleton oF2))))

oJ = Cons ((OCIO "bar") $ oH) (Singleton  . (OCIO "foo") $ oH) 

oK = Lift (Inr (Cons oF2 (Lift (Inl (Cons (OCIO "foo" oK) (Singleton oF2))))))

data Mu :: * -> * -> * where
   Inl :: ObjClass (Tuple (Mu a b) b) -> Mu a b
   Inr :: ObjClass (Tuple a (Mu a b)) -> Mu a b
   Inlx :: Tuple (Mu a b) b -> Mu a b
   Inrx :: Tuple a (Mu a b) -> Mu a b 

prettyOCC :: ObjClassComponent a -> String
prettyOCC (OCFTV fn ty) = fn ++ " " ++ prettyASN ty
prettyOCC (OCIO fn oc)  = fn

prettyASN :: ASNType a -> String
prettyASN BOOLEAN = "BOOLEAN"
prettyASN INTEGER = "INTEGER"

prettyOC :: ObjClass a -> String
prettyOC (Singleton occ) = prettyOCC occ
prettyOC (Cons occ oc) = prettyOCC occ ++ " " ++ prettyOC oc
prettyOC (Lift mu) = prettyMu mu

prettyMu :: Mu a b -> String
prettyMu (Inl oc) = prettyOC oc
prettyMu (Inr oc) = prettyOC oc

f :: ObjClass a -> a -> String
f (Singleton occ) x = undefined

data ObjClassComponent1 :: * -> * where
   OCType :: FieldName -> ObjClassComponent1 a
   OCFixedTypeValue :: FieldName -> ASNType a -> ObjClassComponent1 a
   OCVariableTypeValue :: FieldName -> ObjClassComponent1 a -> ObjClassComponent1 a
   OCFixedTypeValueSet :: FieldName -> ASNType a -> ObjClassComponent1 a
   OCVariableTypeValueSet :: FieldName -> ObjClassComponent1 a -> ObjClassComponent1 a
   OCInformationObject :: FieldName -> ObjClass1 a -> ObjClassComponent1 a

data ObjClass1 :: * -> * where
   Singleton1 :: ObjClassComponent1 a -> ObjClass1 a
   Cons1      :: ObjClassComponent1 a -> ObjClass1 l -> ObjClass1 (Tuple a l)
   Lift1      :: Mu1 a l -> ObjClass1 (Mu1 a l)

data Mu1 :: * -> * -> * where
   Inl1 :: ObjClass1 (Tuple (Mu1 a b) b) -> Mu1 a b
   Inr1 :: ObjClass1 (Tuple a (Mu1 a b)) -> Mu1 a b

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

x = Lift1 (Inr1 (Cons1 x7 (Lift1 (Inl1 (Cons1 (OCInformationObject "other function" x) (Cons1 x6 (Cons1 x5 (Cons1 x4 (Cons1 x3 (Cons1 x2 (Singleton1 x1)))))))))))

printObjClassComp (OCType fn) = text "Type" <+> text fn
printObjClassComp (OCFixedTypeValue fn t) = text "Fixed Type Value" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValue fn c) = text "Variable Type Value" <+> text fn <+> braces (printObjClassComp c)
printObjClassComp (OCFixedTypeValueSet fn t) = text "Fixed Type Value Set" <+> text fn <+> prettyType t
printObjClassComp (OCVariableTypeValueSet fn c) = text "Variable Type Value Set" <+> text fn <+> braces (printObjClassComp c)
printObjClassComp (OCInformationObject fn oc)  = text "Information Object" <+> text fn

prettyOC1 :: ObjClass1 a -> Doc
prettyOC1 (Singleton1 occ) = printObjClassComp occ
prettyOC1 (Cons1 occ oc) = printObjClassComp occ $$ prettyOC1 oc
prettyOC1 (Lift1 mu) = prettyMu1 mu

prettyMu1 :: Mu1 a b -> Doc
prettyMu1 (Inl1 oc) = prettyOC1 oc
prettyMu1 (Inr1 oc) = prettyOC1 oc

{-
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

Thus ALGORITHM is not a type, but a CLASS. On the other hand, ALGORITHM.&id is a type, namely, an OBJECT IDENTIFIER. ALGORITHM.&Type is also a type, an open type. This means it can be various types, but since it is constrained by ({SupportedAlgorithms}{ @algorithm}), it is not just any type, but one that fits the constraint. Let's look at the two elements one at a time.

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

Note the "WITH SYNTAX" in the definition of TYPE-IDENTIFIER above. It describes the way to specify each object as a type (&Type) followed by the string "IDENTIFIED BY" followed by an OBJECT IDENTIFIER (&id). Thus Algo1 is associated with { 1 2 3 4 1 }; Algo2 is associated with { 1 2 3 4 2 }; and Algo3 is associated with { 1 2 3 4 3 }.

I wrote above that ALGORITHM.&id is constrained to be one of the OBJECT IDENTIFIERS in the SupportedAlgorithms object set. Using my example above, you see that it is limited to taking the value of one of the three object identifiers.

ALGORITHM.&Type ({SupportedAlgorithms}{ @algorithm}) is an open type constrained to be one of the types specified in SupportedAlgorithms depending upon algorithm. Bear in mind the definition of algorithm, and you'll see that what


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