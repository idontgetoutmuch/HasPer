\begin{code}
{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
#-}
module ConstraintGeneration where

import ASNTYPE
import LatticeMod
import Control.Monad.Error
\end{code}



Generation of Integer constraints.


-- X.680 G.4.2.3 states that extension additions are discarded if
-- a further constraint is subsequently serially applied.
-- Thus applyExt only requires the last constraint in the list
-- (the last in the serial application) and the root of the parent
-- type since values in extension additions can only be values that
-- are in the root of the parent type. The second element of the
-- returned pair indicates if the constraint is extensible (True) or
-- not (False).

\begin{code}

lApplyExt :: (IC a, Eq a, Lattice a, Show a) =>
             Either String a -> ESS InfInteger -> (Either String a, Bool)
lApplyExt rp (RE _)  = (bottom, False)
lApplyExt rp (EXT _) = (bottom, False)
lApplyExt rp (EXTWITH _ c) = (lApplyExtWithRt rp (lCalcEC c), True)

-- Need to define calcEC (follow rules outlined in X.680 G.4.3.8)
-- and appExtWithRt
-- For Integer constraints, set operators are only applied to
-- non-extensible constraints (see 47.2 and 47.4 for definitions of
-- SingleValue and ValueRange constraints) and thus calcEC is simply
-- calcC. Thus G.4.3.8 can be ignored.

lCalcEC :: (IC a,Lattice a, Show a, Eq a) =>
           Constr InfInteger -> Either String a
lCalcEC c = lCalcC c

-- applyExtWithRt is simply serialC (defined below) since it is
-- the serial application of the parent root and the extension of the
-- final constraint. Only values in the paernt root may appear in the
-- extension (see X.680 section G.4.2.3).

lApplyExtWithRt :: (Eq a, Lattice a, IC a, Show a) =>
                   Either String a -> Either String a -> Either String a
lApplyExtWithRt a b = lSerialC a b

-- need to define encInt

-- Need first input to host incremented constraint (due to serial constraints)
-- Need Either type to deal with legal and illegal constraints. An
-- illegal constraint (typically a mismatch between a parent type and
-- a constraint), will result in a string indicating the problem.
-- Need Maybe type to deal with empty constraint e.g. mutually exclusive intersection
-- As soon as one encounters an illegal constraint this is always
-- returned, and an empty constraint is only superceded by an illegal constraint.
-- Although an empty constraint could be viewed like an illegal
-- constraint (since it does not allow any legal values), this could
-- form either part of an extensible constraint whose overall effect
-- is lega

lRootIntCons :: (IC a, Lattice a, Eq a, Show a) =>
                 Either String a -> [ESS InfInteger] -> Either String a
lRootIntCons x [] = x
lRootIntCons x (c:cs) = lRootIntCons (lEvalC c x) cs

lEvalC ::  (IC a, Lattice a, Eq a, Show a) =>
          ESS InfInteger -> Either String a -> Either String a
lEvalC (RE c) x       = lSerialC x (lCalcC c)
lEvalC (EXT c) x      = lSerialC x (lCalcC c)
lEvalC (EXTWITH c d) x = lSerialC x (lCalcC c)

-- See X.680 section G.4.2.3 for details on the serial application
-- of constraints. The second input is the new constraint whose
-- values must be bounded by the values in the first input. Thus
-- minBound in the second input matches the lower bound in the first
-- input and similarly for maxBound. Note that serialC takes two
-- Maybe type inputs since the illegal first input has already been
-- dealt with by applyIntCons. The second input cannot be illegal
-- since this is simply the (possible) set combination of atomic
-- constraints and involves no serial application of constraints.

lSerialC :: (Show a, Lattice a, IC a, Eq a) =>
            Either String a -> Either String a -> Either String a
lSerialC mx my =
   do a <- mx
      b <- my
      let la = getLower a
          ua = getUpper a
          lb = getLower b
          ub = getUpper b
          foobar
             | not (within a b)
                = throwError ("Constraint and parent type mismatch: " ++ show b ++ " is not within " ++ show a) -- Somehow we should prettyConstraint here
             | otherwise
                = return (serialCombine a b)
      foobar

lCalcC :: (IC a, Lattice a, Eq a, Show a) => Constr InfInteger -> Either String a
lCalcC (UNION u) = lCalcU u

-- Need to define unionC which returns the union of two
-- constraints

lCalcU :: (IC a, Lattice a, Eq a, Show a) => Union InfInteger -> Either String a
lCalcU (IC i) = lCalcI i
lCalcU(UC u i) = (lCalcU u) `ljoin` (lCalcI i)


lCalcI :: (IC a, Lattice a, Eq a, Show a) =>
          IntCon InfInteger -> Either String a
lCalcI (INTER i e) = (lCalcI i) `meet` (lCalcA e)
lCalcI (ATOM a)    = lCalcA a

lCalcA :: (IC a, Lattice a, Eq a, Show a) => IE InfInteger -> Either String a
lCalcA (E e) = lCalcE e

-- Note that the resulting constraint is always a contiguous set.

-- Need processCT to process the constraint implications of type
-- inclusion.
-- NOTE: Need to deal with illegal constraints resulting from
-- processCT

lCalcE :: (IC a, Lattice a, Eq a, Show a) => Elem InfInteger -> Either String a
lCalcE (S (SV i)) = return (makeIC i i)
lCalcE (C (Inc t)) = lProcessCT t []
lCalcE (V (R (l,u))) = return (makeIC l u)



-- Note that a parent type does not inherit the extension of an
-- included type. Thus we use lRootIntCons on the included type.

lProcessCT :: (IC a, Lattice a, Eq a, Show a) =>
              ASNType InfInteger -> [ESS InfInteger] -> Either String a
lProcessCT (BT INTEGER) cl = lRootIntCons top cl
lProcessCT (ConsT t c) cl  = lProcessCT t (c:cl)

\end{code}


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
                     (Elem t1 -> Bool -> t (a (b i))) -> t (a1 (b i)) -> [ESS t1] -> t (a1 (b i))
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
                (Elem t -> Bool -> m (a1 (b i))) -> a (b i) -> ESS t -> m (a2 (b i))
lSerialApply fn ersc c = lEitherApply ersc (lEffCons fn c)

\end{code}

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
        foobar


lSerialApplyLast :: (MonadError [Char] t1,
                     ExtConstraint a1,
                     Lattice (b i),
                     Constraint b i,
                     Eq (b i),
                     ExtConstraint a,
                     ExtConstraint a2) =>
                    (Elem t -> Bool -> t1 (a1 (b i))) -> a (b i) -> ESS t -> t1 (a2 (b i))
lSerialApplyLast fn x c = lLastApply x (lEffCons fn c)


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
                         | not (isExtensible x) = lEitherApply x m
                         | isValid r1 r2 && isValid r1 e2
                            = return (makeEC (updateV r1 r2)
                                                    (updateV r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
         foobar

\end{code}

EffCons generates the effective constraint of a restricted
type constraint.

\begin{code}

lEffCons :: (Eq (b i),
                Constraint b i,
                Lattice (b i),
                ExtConstraint a,
                MonadError [Char] t1) =>
               (Elem t -> Bool -> t1 (a (b i))) -> ESS t -> t1 (a (b i))
lEffCons fn (RE c)         = lCon fn c False
lEffCons fn (EXT c)        = lCon fn c True
lEffCons fn (EXTWITH c e)  = lExtendC (lCon fn c False) (lCon fn e False)

\end{code}

Con processes constraints. Its second input indicates if the
type is extensible.

\begin{code}

lCon :: (MonadError [Char] t1,
            ExtConstraint a,
            Lattice (b i),
            Constraint b i,
            Eq (b i)) =>
           (Elem t -> Bool -> t1 (a (b i))) -> Constr t -> Bool -> t1 (a (b i))
lCon fn (UNION u) b         = lConU fn u b
lCon fn (ALL (EXCEPT e)) b  = lExceptAll top (fn e b)

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
            (Elem t -> Bool -> t1 (a (b i))) -> Union t -> Bool -> t1 (a (b i))
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
            (Elem t -> Bool -> t1 (a (b i))) -> IntCon t -> Bool -> t1 (a (b i))
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
            (Elem t -> Bool -> m (a (b i))) -> IE t -> Bool -> m (a (b i))
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

lResConE :: (RS a,
                IC i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a,
                Builtin a) =>
                Elem a -> Bool ->  Either String (ExtResStringConstraint (ResStringConstraint a i))
lResConE (SZ (SC v)) b            = lEffSize v b
lResConE (P (FR (EXT _))) b       = throwError "Invisible!"
lResConE (P (FR (EXTWITH _ _))) b = throwError "Invisible!"
lResConE (P (FR (RE p)))  b       = lEffCons lPaConE (RE p)
lResConE (C (Inc c)) b            = lProcessCST lResConE c []
lResConE (S (SV v))  b            = throwError "Invisible!"


lBSConE :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            Elem BitString -> Bool -> Either String (ExtBS (ConType i))
lBSConE (SZ (SC v)) b  = lEffSize v b
lBSConE (C (Inc c)) b  = throwError "Invisible!"
lBSConE (S (SV v))  b  = throwError "Invisible!"

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
            IC i,
            Builtin a) =>
            Elem a -> Bool -> Either String (ExtResStringConstraint (ResStringConstraint a i))
lPaConE (V (R (l,u))) b
    = let ls = getString l
          us = getString u
          rs = [head ls..head us]
        in
            return (ExtResStringConstraint (ResStringConstraint (makeString rs) top)
                        (ResStringConstraint top top) b)
lPaConE (C (Inc c)) b = lProcessCST lPaConE c []
lPaConE (S (SV v)) b
   = return (ExtResStringConstraint (ResStringConstraint v top)
                                      (ResStringConstraint top top) b)


lEffSize :: (IC a1,
                Lattice a1,
                Eq a1,
                Show a1,
                Constraint b a1,
                Lattice (b a1),
                ExtConstraint a) =>
               ESS InfInteger -> Bool -> Either String (a (b a1))
lEffSize (RE c) b
    = do ec <- lCalcC c
         return (makeEC (makeSC ec) top b)
lEffSize (EXT c) b
    = do ec <- lCalcC c
         return (makeEC (makeSC ec) top True)
lEffSize (EXTWITH c d) b
    = do r <- lCalcC c
         e <- lCalcC d
         return (makeEC (makeSC r) (makeSC e) True)


lProcessCST :: (Lattice (t1 (a1 (b i))),
                MonadError [Char] t1,
                ExtConstraint a1,
                Eq (b i),
                Constraint b i,
                Lattice (b i)) =>
               (Elem t -> Bool -> t1 (a1 (b i))) -> ASNType t -> [ESS t] -> t1 (a1 (b i))
lProcessCST fn (BT _) cl = lRootStringCons fn top cl
lProcessCST fn (ConsT t c) cl = lProcessCST fn t (c:cl)


lRootStringCons :: (ExtConstraint a,
                    Lattice (b i),
                    Constraint b i,
                    Eq (b i),
                    MonadError [Char] t1) =>
                   (Elem t -> Bool -> t1 (a (b i))) -> t1 (a (b i)) -> [ESS t] -> t1 (a (b i))
lRootStringCons fn t cs
    = let m = lSerialEffCons fn t cs
      in do
            c <- m
            r <- return (getRC c)
            return (makeEC r top False)

\end{code}
