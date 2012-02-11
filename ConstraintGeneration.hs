{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
#-}
module ConstraintGeneration where

import ASNTYPE
import LatticeMod
import Control.Monad.Error

evaluateConstraint :: (MonadError [Char] t,
                      Eq c,
                      Constraint c,
                      Lattice c,
                      ExtConstraint a) =>
                     (Element t1 -> Bool -> t (a c)) -> t (a c)
                        -> [SubtypeConstraint t1] -> t (a c)
evaluateConstraint fn m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = applyLastConstraint fn esrc c
                        foobar1 (f:r) = evaluateConstraint fn (applyConstraint fn esrc f) r
                    foobar1 ls
        foobar


applyConstraint :: (Eq c,
                 Constraint c,
                 Lattice c,
                 MonadError [Char] m,
                 ExtConstraint a) =>
                (Element t -> Bool -> m (a c))
                -> a c
                -> SubtypeConstraint t
                -> m (a c)
applyConstraint fn ersc c
    = catchError (makeConstraint ersc (evaluateSingleConstraint False fn c)) (constraintApplicationError ersc)


makeConstraint :: (MonadError [Char] m,
                 ExtConstraint a,
                 Constraint c,
                 Lattice c) =>
                a c -> m (a c) -> m (a c)
makeConstraint esrc m
        = do
            let foobar
                 = do x <- m
                      let rc2 = getRootConstraint x
                          rc1 = getRootConstraint esrc
                          ext2 = getExtConstraint x
                          foobar1
                              = if isExtensible x && isValid rc1 rc2 && isValid rc1 ext2
                                    || (not . isExtensible) x && isValid rc1 rc2
                                        then return (makeExtensibleConstraint (updateConstraint rc1 rc2) top False)
                                        else throwError "Parent type and constraint mismatch"
                      foobar1
            foobar

constraintApplicationError esrc "Invisible!" = return esrc
constraintApplicationError esrc err          = throwError err


applyLastConstraint :: (Eq c,
                     Constraint c,
                     Lattice c,
                     MonadError [Char] m,
                     ExtConstraint a) =>
                    (Element t -> Bool -> m (a c))
                    -> a c
                    -> SubtypeConstraint t
                    -> m (a c)
applyLastConstraint fn x c
    = catchError (makeFinalConstraint x (evaluateSingleConstraint False fn c)) (constraintApplicationError x)


makeFinalConstraint :: (MonadError [Char] t,
               Lattice c,
               Constraint c,
               ExtConstraint a) =>
              a c -> t (a c) -> t (a c)
makeFinalConstraint esrc m
        = do
           let r1 = getRootConstraint esrc
               foobar
                 = do
                    x <- m
                    let
                       r2 = getRootConstraint x
                       e2 = getExtConstraint x
                       foobar1
                         | (not . isExtensible) x && isValid r1 r2
                            = return (makeExtensibleConstraint (updateConstraint r1 r2) top False)
                         | isExtensible x && isValid r1 r2 && isValid r1 e2
                            = return (makeExtensibleConstraint (updateConstraint r1 r2)
                                                    (updateConstraint r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
           foobar


evaluateSingleConstraint :: (Eq c,
                Constraint c,
                Lattice c,
                ExtConstraint a,
                MonadError [Char] t1) => Bool ->
               (Element t -> Bool -> t1 (a c)) -> SubtypeConstraint t -> t1 (a c)
evaluateSingleConstraint x fn (RootOnly c)              = applySetOperations fn c x
evaluateSingleConstraint _ fn (EmptyExtension c)        = applySetOperations fn c True
evaluateSingleConstraint _ fn (NonEmptyExtension c e)
        = extensibleConstraint (applySetOperations fn c False) (applySetOperations fn e False)


applySetOperations :: (MonadError [Char] t1,
            ExtConstraint a,
            Lattice c,
            Constraint c,
            Eq c) =>
           (Element t -> Bool -> t1 (a c)) -> ElementSetSpec t -> Bool -> t1 (a c)
applySetOperations fn (UnionSet u) b                = applyUnions fn u b
applySetOperations fn (ComplementSet (EXCEPT e)) b  = applyExceptAll (fn e b)


extensibleConstraint :: (MonadError [Char] m,
                Lattice c,
                Constraint c,
                ExtConstraint a) =>
               m (a c) -> m (a c) -> m (a c)
extensibleConstraint m n
    = do
        let foobar
                = do
                    x <- m
                    y <- n
                    let
                        r1 = getRootConstraint x
                        e1 = getExtConstraint x
                        r2 = getRootConstraint y
                        e2 = getExtConstraint y
                        foobar1
                            | not (isExtensible x) && not (isExtensible y)
                                = return (makeExtensibleConstraint r1 (except r2 r1) True)
                            | isExtensible x && not (isExtensible y)
                                = return (makeExtensibleConstraint r1 (except (e1 `ljoin` r2) r1) True)
                            | not (isExtensible x) && isExtensible y
                                = return (makeExtensibleConstraint r1 (except (r2 `ljoin` e2) r1) True)
                            | isExtensible x && isExtensible y
                                = return (makeExtensibleConstraint r1
                                            (except (e1 `ljoin` (r2 `ljoin` e2)) r1) True)
                    foobar1
        catchError foobar (\err -> throwError "Invisible")


applyExceptAll :: (MonadError [Char] m,
                  Constraint c,
                  Eq c,
                  Lattice c,
                  ExtConstraint a) =>
                 m (a c) -> m (a c)
applyExceptAll m
    = do
         let foobar
                = do
                    ersc <- m
                    let rc = getRootConstraint ersc
                        emptyConstraint = rc == bottom
                        foobar1
                            | emptyConstraint = return (makeExtensibleConstraint top top False)
                            | otherwise = return (makeExtensibleConstraint (except top rc) top False)
                    foobar1
         catchError foobar (\err -> return (makeExtensibleConstraint top top False))


applyUnions :: (Constraint c,
             Lattice c,
             ExtConstraint a,
             MonadError [Char] t1) =>
            (Element t -> Bool -> t1 (a c)) -> Unions t -> Bool -> t1 (a c)
applyUnions fn (NoUnion i) b     = applyIntersections fn i b
applyUnions fn (UnionMark u i) b = unionConstraints (applyIntersections fn i b) (applyUnions fn u False)


unionConstraints :: (MonadError [Char] m,
               Constraint c,
               Lattice c,
               ExtConstraint a) =>
              m (a c) -> m (a c) -> m (a c)
unionConstraints m n
    = do
        let foobar
             = do
                c1 <- m
                c2 <- n
                let r1 = getRootConstraint c1
                    e1 = getExtConstraint c1
                    r2 = getRootConstraint c2
                    e2 = getExtConstraint c2
                    foobar1
                        | not (isExtensible c1) && not (isExtensible c2)
                             = return (makeExtensibleConstraint (r1 `ljoin` r2) top False)
                        | not (isExtensible c1)
                             = return (makeExtensibleConstraint (r1 `ljoin` r2) e2 True)
                        | isExtensible c1 && not (isExtensible c2)
                             = return (makeExtensibleConstraint (r1 `ljoin` r2) e1 True)
                        | otherwise
                             = return (makeExtensibleConstraint (r1 `ljoin` r2)
                                       (except ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2))
                                                  (r1 `ljoin` r2)) True)
                foobar1
        catchError foobar (\err -> throwError "Invisible")


applyIntersections :: (MonadError [Char] t1,
             ExtConstraint a,
             Lattice c,
             Constraint c) =>
            (Element t -> Bool -> t1 (a c)) -> Intersections t -> Bool -> t1 (a c)
applyIntersections fn (NoIntersection e) b    = intersectionElements fn e b
applyIntersections fn (IntersectionMark i e) b
    = intersectionConstraints (intersectionElements fn e b) (applyIntersections fn i False)


intersectionConstraints :: (Lattice c,
               Constraint c,
               MonadError e t,
               ExtConstraint a) =>
              t (a c) -> t (a c) -> t (a c)
intersectionConstraints m n
    = do
         let foobar1 x
                 = do catchError (do c2 <- n
                                     foobar2 x c2)
                                 (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = getRootConstraint c1
                        e1 = getExtConstraint c1
                        r2 = getRootConstraint c2
                        e2 = getExtConstraint c2
                        foobar3
                            | not (isExtensible c1) && not (isExtensible c2)
                                 = return (makeExtensibleConstraint (r1 `meet` r2) top False)
                            | not (isExtensible c1)
                                 = return (makeExtensibleConstraint (r1 `meet` r2) (r1 `meet` e2) True)
                            | isExtensible c1 && not (isExtensible c2)
                                 = return (makeExtensibleConstraint (r1 `meet` r2) (r2 `meet` e1)  True)
                            | otherwise
                                 = return (makeExtensibleConstraint (r1 `meet` r2) (except ((r1 `ljoin` e1)
                                        `meet` (r2 `ljoin` e2)) (r1 `meet` r2)) True)
                    foobar3
             foobar
                = catchError (do c1 <- m
                                 foobar1 c1)
                             (\err -> n)
         foobar


intersectionElements :: (ExtConstraint a,
             MonadError [Char] m,
             Lattice c,
             Constraint c) =>
            (Element t -> Bool -> m (a c)) -> IntersectionElements t -> Bool -> m (a c)
intersectionElements fn (ElementConstraint e) b  = fn e b
intersectionElements fn (ExclusionConstraint e (EXCEPT ex)) b
                = exceptConstraints (fn e b) (fn ex False)


exceptConstraints  :: (Constraint c,
                ExtConstraint a,
                Lattice c,
                MonadError [Char] m) =>
               m (a c) -> m (a c) -> m (a c)
exceptConstraints  m n
    = do
         let foobar1 x
                 = catchError (do c2 <- n
                                  foobar2 x c2)
                              (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = getRootConstraint c1
                        e1 = getExtConstraint c1
                        r2 = getRootConstraint c2
                        e2 = getExtConstraint c2
                        foobar3
                            | not (isExtensible c1)
                                = return (makeExtensibleConstraint (except r1 r2) top False)
                            | isExtensible c1 && not (isExtensible c2)
                                 = return (makeExtensibleConstraint (except r1 r2)
                                            (except (except r1 e2) (except r1 r2)) True)
                            | otherwise
                                 = return (makeExtensibleConstraint (except r1 r2)
                                            (except (except r1 (r2 `ljoin` e2))
                                                       (except r1 r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> throwError "Invisible")
         foobar


booleanElements :: Element Bool -> Bool -> Either String (ExtensibleConstraint BooleanConstraint)
booleanElements (S (SV i)) b
    = return (makeExtensibleConstraint
                (BooleanConstraint [i]) top b)
booleanElements (C (Inc t)) b
    = containedBooleanType t []


containedBooleanType :: ASNType Bool -> [SubtypeConstraint Bool]
               -> Either String (ExtensibleConstraint BooleanConstraint)
containedBooleanType (BuiltinType BOOLEAN) cl
    =  let  tp = ExtensibleConstraint top top False
            tpp = Right tp
        in
                extensionRootOnly $ evaluateConstraint booleanElements tpp cl
containedBooleanType (ConstrainedType t c) cl
    = containedBooleanType t (c:cl)


pvIntegerElements :: (Constraint a, IntegerCon a, Lattice a, Eq a, Show a)
    => Element InfInteger -> Bool -> Either String (ExtensibleConstraint a)
pvIntegerElements (S (SV i)) b
    = return (makeExtensibleConstraint
                (makeIntegerConstraint i i) top b)
pvIntegerElements (C (Inc t)) b
    = containedIntegerType t []
pvIntegerElements (V (R (l,u))) b
    = return (makeExtensibleConstraint
                (makeIntegerConstraint l u) top b)


containedIntegerType :: (Constraint a, IntegerCon a, Lattice a, Eq a, Show a) =>
              ASNType InfInteger -> [SubtypeConstraint InfInteger]
               -> Either String (ExtensibleConstraint a)
containedIntegerType (BuiltinType INTEGER) cl
    =   let t = makeIntegerConstraint NegInf PosInf
            tp = ExtensibleConstraint t t False
            tpp = Right tp
        in
            extensionRootOnly $ evaluateConstraint pvIntegerElements tpp cl
containedIntegerType (ConstrainedType t c) cl
    = containedIntegerType t (c:cl)

extensionRootOnly :: Lattice a =>
                     Either String (ExtensibleConstraint a) -> Either String (ExtensibleConstraint a)
extensionRootOnly (Right (ExtensibleConstraint r e b))
   =     Right (ExtensibleConstraint r top False)
extensionRootOnly x = x


enumeratedElements :: Enumerate -> Element Name -> Bool -> Either String (ExtensibleConstraint EnumeratedConstraint)
enumeratedElements en (S (SV nm)) b
    = let (b, p) = validEnum en nm 0				 
          indices = (snd . assignIndex) en
			in if b
            then 
                let Just pos = p
                    i = indices !! pos
							  in	return (makeExtensibleConstraint (EnumeratedConstraint [i]) top b)
	 					else
							  throwError "Invalid enumeration"
enumeratedElements en (C (Inc t)) b
    = containedEnumeratedType en t []

		
validEnum :: Enumerate -> Name -> Int -> (Bool, Maybe Int)
validEnum EmptyEnumeration nm n = (False, Nothing)
validEnum (AddEnumeration e r) nm n
					| getName e == nm = (True, Just n)
					| otherwise = validEnum r nm (n+1) 
validEnum (EnumerationExtensionMarker e) nm n
					= validEnum e nm n
						

containedEnumeratedType :: Enumerate -> ASNType Name -> [SubtypeConstraint Name]
               -> Either String (ExtensibleConstraint EnumeratedConstraint)
containedEnumeratedType en (BuiltinType (ENUMERATED e)) cl
    =  let  tp = ExtensibleConstraint top top False
            tpp = Right tp
        in
					if en == e
						 then
                extensionRootOnly $ evaluateConstraint (enumeratedElements en) tpp cl
						 else 
						 			throwError "Constraint type does not match required type"
containedEnumeratedType en (ConstrainedType t c) cl
    = containedEnumeratedType en t (c:cl)


pvBitStringElements :: (Constraint i,
            Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element BitString -> Bool -> Either String (ExtensibleConstraint i)
pvBitStringElements (SZ (SC v)) b  = evaluateSingleConstraint b pvIntegerElements v
pvBitStringElements (C (Inc c)) b  = throwError "Invisible!"
pvBitStringElements (S (SV v))  b  = throwError "Invisible!"


pvOctetStringElements :: (Constraint i,
            Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element OctetString -> Bool -> Either String (ExtensibleConstraint i)
pvOctetStringElements (SZ (SC v)) b  = evaluateSingleConstraint b pvIntegerElements v
pvOctetStringElements (C (Inc c)) b  = throwError "Invisible!"
pvOctetStringElements (S (SV v))  b  = throwError "Invisible!"

pvKnownMultiplierElements :: (Constraint i,
             RS a,
                IntegerCon i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) =>
                Element a -> Bool ->  Either String (ExtensibleConstraint (ResStringConstraint a i))
pvKnownMultiplierElements (SZ (SC v)) b
    = integerToKMConstraint $ evaluateSingleConstraint b pvIntegerElements v
pvKnownMultiplierElements (P (FR (EmptyExtension _))) b
    = throwError "Invisible!"
pvKnownMultiplierElements (P (FR (NonEmptyExtension _ _))) b
    = throwError "Invisible!"
pvKnownMultiplierElements (P (FR (RootOnly p)))  b
    = evaluateSingleConstraint b pvPermittedAlphabetElements (RootOnly p)
pvKnownMultiplierElements (C (Inc c)) b
    = containedKnownMultType c []
pvKnownMultiplierElements (S (SV v))  b
    = throwError "Invisible!"


pvPermittedAlphabetElements :: (Lattice a,
            Lattice i,
            Constraint i,
            RS a,
            Eq a,
            Eq i,
            Show i,
            IntegerCon i) =>
            Element a -> Bool -> Either String (ExtensibleConstraint (ResStringConstraint a i))
pvPermittedAlphabetElements (V (R (l,u))) b
    = let ls = getString l
          us = getString u
          rs = [head ls..head us]
        in
            return (ExtensibleConstraint (ResStringConstraint (makeString rs) top)
                        (ResStringConstraint top top) b)
pvPermittedAlphabetElements (C (Inc c)) b
    = containedKnownMultType c []
pvPermittedAlphabetElements (S (SV v)) b
    = return (ExtensibleConstraint (ResStringConstraint v top)
                                      (ResStringConstraint top top) b)


integerToKMConstraint :: (RS a,
                IntegerCon i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) => Either String (ExtensibleConstraint i)
                         -> Either String (ExtensibleConstraint (ResStringConstraint a i))
integerToKMConstraint (Right (ExtensibleConstraint x y b))
    = Right (ExtensibleConstraint (ResStringConstraint top x) (ResStringConstraint top y) b)
integerToKMConstraint (Left s) = Left s


containedKnownMultType :: (RS a,
                Eq c,
                                Show c,
                Constraint c,
                Lattice c,
                Lattice a,
                Eq a,
                IntegerCon c) =>
                ASNType a -> [SubtypeConstraint a] -> Either String (ExtensibleConstraint (ResStringConstraint a c))
containedKnownMultType (BuiltinType _) cl
            =   let t = ResStringConstraint top top
                    tp = ExtensibleConstraint t t False
                    tpp = Right tp
                in
                                    extensionRootOnly $ evaluateConstraint pvKnownMultiplierElements tpp cl
containedKnownMultType (ConstrainedType t c) cl
                                             = containedKnownMultType t (c:cl)


pvSequenceOfElements :: (Constraint i,
            Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element [a] -> Bool -> Either String (ExtensibleConstraint i)
pvSequenceOfElements (SZ (SC v)) b  = evaluateSingleConstraint b pvIntegerElements v
pvSequenceOfElements (C (Inc c)) b  = throwError "Invisible!"
pvSequenceOfElements (S (SV v))  b  = throwError "Invisible!"
pvSequenceOfElements (IT (WC c)) b  = throwError "Invisible!"
pvSequenceOfElements (IT WCS) b     = throwError "Invisible!"
