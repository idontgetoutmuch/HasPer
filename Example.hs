data ZeroTuple = ZeroTuple
data Tuple e es = Tuple e es

newtype IA5String = IA5String {unIA5String :: String}

data ASNType :: * -> * where
   BOOLEAN   :: ASNType Bool
   INTEGER   :: ASNType Integer
   IA5STRING :: ASNType IA5String

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

oG = Lift (Inr (Cons oF2 (Singleton (OCIO "another" oG))))

oH = Lift (Inl (Cons (OCIO "another" oH) (Cons oF2 (Singleton oF2))))

oJ = Cons ((OCIO "bar") $ oH) (Singleton  . (OCIO "foo") $ oH) 

oK = Lift (Inr (Cons oF2 (Lift (Inl (Cons (OCIO "foo" oK) (Singleton oF2))))))

data Mu :: * -> * -> * where
   Inl :: ObjClass (Tuple (Mu a b) b) -> Mu a b
   Inr :: ObjClass (Tuple a (Mu a b)) -> Mu a b

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

data ObjClassComponent1 :: * -> * where
   OCType :: FieldName -> ObjClassComponent1 a
   OCFixedTypeValue :: FieldName -> ASNType a -> ObjClassComponent1 a
   OCVariableTypeValue :: FieldName -> ObjClassComponent1 a -> ObjClassComponent1 a
   OCFixedTypeValueSet :: FieldName -> ASNType a -> ObjClassComponent1 a
   OCVariableTypeValueSet :: FieldName -> ObjClassComponent1 a -> ObjClassComponent1 a
   OCInformationObject :: FieldName -> ObjClass1 a -> ObjClassComponent1 a

x1 = OCType "ArgumentType"
x2 = OCFixedTypeValue "code" INTEGER
x3 = OCType "ResultType"
x4 = OCVariableTypeValue "result-if-error" x3
x5 = OCFixedTypeValueSet "Alphabet" IA5STRING
x6 = OCVariableTypeValueSet "Supported Arguments" x1
x7 = OCFixedTypeValueSet "Errors" BOOLEAN

data ObjClass1 :: * -> * where
   Singleton1 :: ObjClassComponent1 a -> ObjClass1 a
   Cons1      :: ObjClassComponent1 a -> ObjClass1 l -> ObjClass1 (Tuple a l)
   Lift1      :: Mu1 a l -> ObjClass1 (Mu1 a l)

data Mu1 :: * -> * -> * where
   Inl1 :: ObjClass1 (Tuple (Mu1 a b) b) -> Mu1 a b
   Inr1 :: ObjClass1 (Tuple a (Mu1 a b)) -> Mu1 a b

x = Lift1 (Inl1 (Cons1 (OCInformationObject "other function" x) (Cons1 x6 (Cons1 x5 (Cons1 x4 (Cons1 x3 (Cons1 x2 (Singleton1 x1))))))))