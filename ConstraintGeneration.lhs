\begin{code}
{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
#-}
module ConstraintGeneration where

import ASNTYPE
import LatticeMod
import Control.Monad.Error
\end{code}





GENERATION OF EFFECTIVE STRING CONSTRAINT

 resEffCons takes a restricted string constraint and returns either a pair
 of effective constraints or a message indicating that the constraint is
 not PER-visible. The pair includes the
 effective size constraint and the effective permitted alphabet
 constraint. The evaluation takes account of the effect of set
 operators and extensibility. Note that extensible size and
 permitted alphabet constraints may be combined using set operators
 which is not the case for an Integer value range constraint.
 The return type is a pair of ResStringContraint values - the first for
 the root constraint and the second for the extension constraint -
 paired with a boolean value that indicates whether an extension is
 expected (hence a bit prefix in the encoding) or not.
 ResStringConstraint is a parameterised type (to allow for the different restricted string types)
 encompassing the (size,permittedAlphabet) constraint pair.


serialEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

{- NOTE WE WANT THE TYPE TO BE MORE GENERAL e.g. replaced VisibleString with RS a => a -}

serialEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

\begin{code}

lSerialEffCons :: (MonadError [Char] t,
                      ExtConstraint a1,
                      Eq (b i),
                      Constraint b i,
                      Lattice (b i),
                      ExtConstraint a) =>
                     (Element t1 -> Bool -> t (a (b i))) -> t (a1 (b i))
                        -> [SubtypeConstraint t1] -> t (a1 (b i))
lSerialEffCons fn m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = lSerialApplyLast fn esrc c
                        foobar1 (f:r) = lSerialEffCons fn (lSerialApply fn esrc f) r
                    foobar1 ls
        foobar


lSerialApply :: (MonadError [Char] m,
                 ExtConstraint a1,
                 Lattice (b i),
                 Constraint b i,
                 Eq (b i),
                 ExtConstraint a2,
                 ExtConstraint a) =>
                (Element t -> Bool -> m (a1 (b i))) -> a (b i) -> SubtypeConstraint t -> m (a2 (b i))
lSerialApply fn ersc c = lEitherApply ersc (lEffCons False fn c)

\end{code}
Note that if a complete constraint in serial application is not PER-visible then it is simply
ignored (X.691 B.2.2.2).

\begin{code}

lEitherApply :: (MonadError [Char] m,
                 ExtConstraint a,
                 ExtConstraint a1,
                 Constraint b i,
                 Lattice (b i),
                 ExtConstraint a2) =>
                a (b i) -> m (a1 (b i)) -> m (a2 (b i))
lEitherApply esrc m
    = do
        let foobar
                = do x <- m
                     let rc2 = getRC x
                         rc1 = getRC esrc
                         foobar1
                            = if isValid rc1 rc2
                                 then return (makeEC (updateV rc1 rc2) top False)
                                 else throwError "Parent type and constraint mismatch"
                     foobar1
        catchError foobar (\err -> return (makeEC (getRC esrc) top False) )



lSerialApplyLast :: (MonadError [Char] t1,
                     ExtConstraint a1,
                     Lattice (b i),
                     Constraint b i,
                     Eq (b i),
                     ExtConstraint a,
                     ExtConstraint a2) =>
                    (Element t -> Bool -> t1 (a1 (b i))) -> a (b i) -> SubtypeConstraint t -> t1 (a2 (b i))
lSerialApplyLast fn x c = lLastApply x (lEffCons False fn c)


lLastApply :: (MonadError [Char] t,
               ExtConstraint a1,
               ExtConstraint a2,
               Lattice (b i),
               Constraint b i,
               ExtConstraint a) =>
              a (b i) -> t (a1 (b i)) -> t (a2 (b i))
lLastApply esrc m
    = do
         let  r1 = getRC esrc
              foobar
                 = do
                    x <- m
                    let
                       r2 = getRC x
                       e2 = getEC x
                       foobar1
                         | not (isExtensible x) = lEitherApply esrc m
                         | isValid r1 r2 && isValid r1 e2
                            = return (makeEC (updateV r1 r2)
                                                    (updateV r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
         catchError foobar (\err -> return (makeEC (getRC esrc) top False) )

\end{code}

EffCons generates the effective constraint of a restricted
type constraint.

\begin{code}

lEffCons :: (Eq (b i),
                Constraint b i,
                Lattice (b i),
                ExtConstraint a,
                MonadError [Char] t1) => Bool ->
               (Element t -> Bool -> t1 (a (b i))) -> SubtypeConstraint t -> t1 (a (b i))
lEffCons x fn (RootOnly c)         = lCon fn c x
lEffCons _ fn (EmptyExtension c)        = lCon fn c True
lEffCons _ fn (NonEmptyExtension c e)  = lExtendC (lCon fn c False) (lCon fn e False)

\end{code}

Con processes constraints. Its second input indicates if the
type is extensible.

\begin{code}

lCon :: (MonadError [Char] t1,
            ExtConstraint a,
            Lattice (b i),
            Constraint b i,
            Eq (b i)) =>
           (Element t -> Bool -> t1 (a (b i))) -> ConstraintSet t -> Bool -> t1 (a (b i))
lCon fn (UnionSet u) b         = lConU fn u b
lCon fn (ComplementSet (EXCEPT e)) b  = lExceptAll top (fn e b)

\end{code}

extendC implements the extension operator (...) on visiblestring
constraints.
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)

\begin{code}

lExtendC :: (MonadError [Char] m,
                Lattice (b i),
                ExtConstraint a2,
                Constraint b i,
                ExtConstraint a1,
                ExtConstraint a) =>
               m (a1 (b i)) -> m (a (b i)) -> m (a2 (b i))
lExtendC m n
    = do
        let foobar
                = do
                    x <- m
                    y <- n
                    let
                        r1 = getRC x
                        e1 = getEC x
                        r2 = getRC y
                        e2 = getEC y
                        foobar1
                            | not (isExtensible x) && not (isExtensible y)
                                = return (makeEC r1 (except r2 r1) True)
                            | isExtensible x && not (isExtensible y)
                                = return (makeEC r1 (except (e1 `ljoin` r2) r1) True)
                            | not (isExtensible x) && isExtensible y
                                = return (makeEC r1 (except (r2 `ljoin` e2) r1) True)
                            | isExtensible x && isExtensible y
                                = return (makeEC r1
                                            (except (e1 `ljoin` (r2 `ljoin` e2)) r1) True)
                    foobar1
        catchError foobar (\err -> throwError "Invisible")

\end{code}

ExceptAll has to deal with the various potential universal
sets which are dependent on the nature of the excepted constraint.
Note: The resulting constraint is non-extensible (see X.680
G.4.3.8)

\begin{code}

lExceptAll :: (MonadError [Char] m,
                  Constraint b i,
                  ExtConstraint a1,
                  Eq (b i),
                  Lattice (b i),
                  ExtConstraint a) =>
                 b i -> m (a (b i)) -> m (a1 (b i))
lExceptAll t m
    = do
         let foobar
                = do
                    ersc <- m
                    let rc = getRC ersc
                        emptyConstraint = rc == bottom
                        foobar1
                            | emptyConstraint = return (makeEC t top False)
                            | otherwise = return (makeEC (except top rc) top False)
                    foobar1
         catchError foobar (\err -> throwError "Invisible")


lConU :: (Constraint b i,
             Lattice (b i),
             ExtConstraint a,
             MonadError [Char] t1) =>
            (Element t -> Bool -> t1 (a (b i))) -> Union t -> Bool -> t1 (a (b i))
lConU fn (IC i) b   = lConI fn i b
lConU fn (UC u i) b = lUnionC (lConI fn i b) (lConU fn u False)

\end{code}

union returns the union of two pairs of constraints. Note
that the union of a size constraint (and no permitted alphabet constraint)
and vice versa result in no constraint.
sizeUnion and paUnion union size and permitted alphabet constraints respectively.

unionresC implements the union operator on visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680) Note that a union of a size constraint and a permitted
alphabet constraint is an unconstrained type.

\begin{code}

lUnionC :: (MonadError [Char] m,
               Constraint b i,
               ExtConstraint a2,
               Lattice (b i),
               ExtConstraint a1,
               ExtConstraint a) =>
              m (a1 (b i)) -> m (a (b i)) -> m (a2 (b i))
lUnionC m n
    = do
        let foobar
             = do
                c1 <- m
                c2 <- n
                let r1 = getRC c1
                    e1 = getEC c1
                    r2 = getRC c2
                    e2 = getEC c2
                    foobar1
                        | not (isExtensible c1) && not (isExtensible c2)
                             = return (makeEC (r1 `ljoin` r2) top False)
                        | not (isExtensible c1)
                             = return (makeEC (r1 `ljoin` r2) e2 True)
                        | isExtensible c1 && not (isExtensible c2)
                             = return (makeEC (r1 `ljoin` r2) e1 True)
                        | otherwise
                             = return (makeEC (r1 `ljoin` r2)
                                       (except ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2))
                                                  (r1 `ljoin` r2)) True)
                foobar1
        catchError foobar (\err -> throwError "Invisible")

\end{code}

ConI deals with the intersection of visiblestring constraints

\begin{code}

lConI :: (MonadError [Char] t1,
             ExtConstraint a,
             Lattice (b i),
             Constraint b i) =>
            (Element t -> Bool -> t1 (a (b i))) -> Intersection t -> Bool -> t1 (a (b i))
lConI fn (INTER i e) b = lInterC (lConA fn e b) (lConI fn i False)
lConI fn (ATOM e) b    = lConA fn e b

\end{code}

interC implements the intersection of visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lInterC :: (Lattice (b i),
               Constraint b i,
               MonadError e t,
               ExtConstraint a) =>
              t (a (b i)) -> t (a (b i)) -> t (a (b i))
lInterC m n
    = do
         let foobar1 x
                 = do catchError (do c2 <- n
                                     foobar2 x c2)
                                 (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = getRC c1
                        e1 = getEC c1
                        r2 = getRC c2
                        e2 = getEC c2
                        foobar3
                            | not (isExtensible c1) && not (isExtensible c2)
                                 = return (makeEC (r1 `meet` r2) top False)
                            | not (isExtensible c1)
                                 = return (makeEC (r1 `meet` r2) (r1 `meet` e2) True)
                            | isExtensible c1 && not (isExtensible c2)
                                 = return (makeEC (r1 `meet` r2) (r2 `meet` e1)  True)
                            | otherwise
                                 = return (makeEC (r1 `meet` r2) (except ((r1 `ljoin` e1)
                                        `meet` (r2 `ljoin` e2)) (r1 `meet` r2)) True)
                    foobar3
             foobar
                = catchError (do c1 <- m
                                 foobar1 c1)
                             (\err -> n)
         foobar

\end{code}

ConA deals with atomic (including except) constraints

\begin{code}

lConA :: (ExtConstraint a,
             MonadError [Char] m,
             Lattice (b i),
             Constraint b i) =>
            (Element t -> Bool -> m (a (b i))) -> IE t -> Bool -> m (a (b i))
lConA fn (E e) b  = fn e b
lConA fn (Exc e (EXCEPT ex)) b
                = lExceptC (fn e b) (fn ex False)

\end{code}

Except implements the set difference operator applied to
visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lExceptC :: (Constraint b i,
                ExtConstraint a,
                Lattice (b i),
                MonadError [Char] m,
                ExtConstraint a1) =>
               m (a1 (b i)) -> m (a (b i)) -> m (a1 (b i))
lExceptC m n
    = do
         let foobar1 x
                 = catchError (do c2 <- n
                                  foobar2 x c2)
                              (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = getRC c1
                        e1 = getEC c1
                        r2 = getRC c2
                        e2 = getEC c2
                        foobar3
                            | not (isExtensible c1)
                                = return (makeEC (except r1 r2) top False)
                            | isExtensible c1 && not (isExtensible c2)
                                 = return (makeEC (except r1 r2)
                                            (except (except r1 e2) (except r1 r2)) True)
                            | otherwise
                                 = return (makeEC (except r1 r2)
                                            (except (except r1 (r2 `ljoin` e2))
                                                       (except r1 r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> throwError "Invisible")
         foobar

\end{code}

ConE deals with the various visiblestring constraints
Note that a permitted alphabet constraint uses value range
constraint(s) and that extensible permitted alphabet
constraints are not per-visible.
The first case (size-constraint) we can make use of the
functions that create an effective Integer constraint. We
cannot use evalC since it includes serial application of
constraints.

\begin{code}


integerConElements :: (IC a, Lattice a, Eq a, Show a) => Element InfInteger -> Bool ->
                Either String (ExtBS (ConType a))
integerConElements (S (SV i)) b = return (makeEC (makeSC $ makeIC i i) top b)
integerConElements (C (Inc t)) b  = lProcessCT t []
integerConElements (V (R (l,u))) b = return (makeEC (makeSC $ makeIC l u) top b)

-- {- FIXME Parent type does not inherit extension of included type -}

lProcessCT :: (IC a, Lattice a, Eq a, Show a) =>
              ASNType InfInteger -> [SubtypeConstraint InfInteger] -> Either String (ExtBS (ConType a))
lProcessCT (BuiltinType INTEGER) cl = lSerialEffCons integerConElements top cl
lProcessCT (ConstrainedType t c) cl  = lProcessCT t (c:cl)

{- FIXME: Note that boolean input is thrown away -}

lResConE :: (RS a,
                IC i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) =>
                Element a -> Bool ->  Either String (ExtResStringConstraint (ResStringConstraint a i))
lResConE (SZ (SC v)) b            = convertIntToRS $ lEffCons b integerConElements v
lResConE (P (FR (EmptyExtension _))) b       = throwError "Invisible!"
lResConE (P (FR (NonEmptyExtension _ _))) b = throwError "Invisible!"
lResConE (P (FR (RootOnly p)))  b       = lEffCons b lPaConE (RootOnly p)
lResConE (C (Inc c)) b            = lProcessCST lResConE c []
lResConE (S (SV v))  b            = throwError "Invisible!"


convertIntToRS :: (RS a,
                IC i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) => Either String (ExtBS (ConType i))
                         -> Either String (ExtResStringConstraint (ResStringConstraint a i))
convertIntToRS (Right (ExtBS (ConType x) (ConType y) b))
    = Right (ExtResStringConstraint (ResStringConstraint top x) (ResStringConstraint top y) b)
convertIntToRS (Left s) = Left s

{- FIXME: Note that boolean is thrown away -}

lBSConE :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            Element BitString -> Bool -> Either String (ExtBS (ConType i))
lBSConE (SZ (SC v)) b  = lEffCons b integerConElements v
lBSConE (C (Inc c)) b  = throwError "Invisible!"
lBSConE (S (SV v))  b  = throwError "Invisible!"

{- FIXME: Note that boolean input is thrown away -}
lOSConE :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            Element OctetString -> Bool -> Either String (ExtBS (ConType i))
lOSConE (SZ (SC v)) b  = lEffCons b integerConElements v
lOSConE (C (Inc c)) b  = throwError "Invisible!"
lOSConE (S (SV v))  b  = throwError "Invisible!"

\end{code}

paConE deals with the various visiblestring constraints
Note that a permitted alphabet constraint uses value range
constraint(s) and that extensible permitted alphabet
constraints are not per-visible.
The first case (size-constraint) we can make use of the
functions that create an effective Integer constraint. We
cannot use evalC since it includes serial application of
constraints.

\begin{code}

lPaConE :: (Lattice a,
            Lattice i,
            RS a,
            Eq a,
            Eq i,
            Show i,
            IC i) =>
            Element a -> Bool -> Either String (ExtResStringConstraint (ResStringConstraint a i))
lPaConE (V (R (l,u))) b
    = let ls = getString l
          us = getString u
          rs = [head ls..head us]
        in
            return (ExtResStringConstraint (ResStringConstraint (makeString rs) bottom)
                        (ResStringConstraint top top) b)
lPaConE (C (Inc c)) b = lProcessCST lPaConE c []
lPaConE (S (SV v)) b
   = return (ExtResStringConstraint (ResStringConstraint v top)
                                      (ResStringConstraint top top) b)

{- FIXME: Note that boolean value is thrown away -}

lSeqOfConE :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            Element [a] -> Bool -> Either String (ExtBS (ConType i))
lSeqOfConE (SZ (SC v)) b  = lEffCons b integerConElements v
lSeqOfConE (C (Inc c)) b  = throwError "Invisible!"
lSeqOfConE (S (SV v))  b  = throwError "Invisible!"
lSeqOfConE (IT (WC c)) b  = throwError "Invisible!"
lSeqOfConE (IT WCS) b     = throwError "Invisible!"






lProcessCST :: (Lattice (t1 (a1 (b i))),
                MonadError [Char] t1,
                ExtConstraint a1,
                Eq (b i),
                Constraint b i,
                Lattice (b i)) =>
               (Element t -> Bool -> t1 (a1 (b i))) -> ASNType t -> [SubtypeConstraint t] -> t1 (a1 (b i))
lProcessCST fn (BuiltinType _) cl = lRootStringCons fn top cl
lProcessCST fn (ConstrainedType t c) cl = lProcessCST fn t (c:cl)


lRootStringCons :: (ExtConstraint a,
                    Lattice (b i),
                    Constraint b i,
                    Eq (b i),
                    MonadError [Char] t1) =>
                   (Element t -> Bool -> t1 (a (b i))) -> t1 (a (b i)) -> [SubtypeConstraint t] -> t1 (a (b i))
lRootStringCons fn t cs
    = let m = lSerialEffCons fn t cs
      in do
            c <- m
            r <- return (getRC c)
            return (makeEC r top False)

\end{code}
