\begin{code}
module ConstraintGeneration where

import LatticeMod
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


serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

{- NOTE WE WANT THE TYPE TO BE MORE GENERAL e.g. replaced VisibleString with RS a => a -}

serialResEffCons takes a list of constraints (representing
serially applied constraints) and generates the resulting
effective constraint (if it exists).

\begin{code}

lSerialResEffCons :: (Eq t1,
                      Eq t,
                      Show t,
                      Lattice t1,
                      Lattice t,
                      IC t,
                      RS t1) =>
                      Either String (ExtResStringConstraint t t1) -> [ESS t1]
                      -> Either String (ExtResStringConstraint t t1)
lSerialResEffCons m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = lSerialApplyLast esrc c
                        foobar1 (f:r) = lSerialResEffCons (lSerialApply esrc f) r
                    foobar1 ls
        foobar

lSerialBSEffCons :: ( Eq t,
                      Show t,
                      Lattice t,
                      IC t) =>
                      Either String (ExtBS t) -> [ESS BitString]
                      -> Either String (ExtBS t)
lSerialBSEffCons m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = lSerialApplyLastBS esrc c
                        foobar1 (f:r) = lSerialBSEffCons (lSerialApplyBS esrc f) r
                    foobar1 ls
        foobar

lSerialApply :: (Eq a,
                 Eq t,
                 Show t,
                 Lattice t,
                 Lattice a,
                 IC t,
                 RS a) =>
                 ExtResStringConstraint t a -> ESS a
                 -> Either String (ExtResStringConstraint t a)
lSerialApply ersc c = lEitherApply ersc (lResEffCons c 0)

lSerialApplyBS ::(Eq t,
                 Show t,
                 Lattice t,
                 IC) =>
                 ExtBS t -> ESS BitString -> Either String (ExtBS t)
lSerialApplyBS ersc c = lEitherApplyBS ersc (lBSEffCons c)

\end{code}

\begin{code}

lEitherApply :: (Eq i,
                 Eq a,
                 Show i,
                 Lattice i,
                 Lattice a,
                 IC i,
                 RS a) =>
                 ExtResStringConstraint i a -> Either String (ExtResStringConstraint i a)
                 -> Either String (ExtResStringConstraint i a)
lEitherApply (ExtResStringConstraint rc1 _ _) m
    = do
        let foobar
                = do x <- m
                     let rc2 = getRC x
                         foobar1
                            = if lValidResCon rc1 rc2
                                 then return (ExtResStringConstraint (lUpdateResCon rc1 rc2) top False)
                                 else throwError "Parent type and constraint mismatch"
                     foobar1
        foobar

lEitherApplyBS :: (Eq i,
                   Show i,
                   Lattice i,
                   IC i) =>
                   ExtBS i -> Either String i -> Either String (ExtBS i)
lEitherApplyBS  (ExtBS rc1 _ _) m
    = do
        let foobar
                = do x <- m
                     let rc2 = getBSRC x
                         foobar1
                            = if within rc1 rc2
                                 then return (ExtBS (serialCombine rc1 rc2) top False)
                                 else throwError "Parent type and constraint mismatch"
                     foobar1
        foobar


--lValidResCon :: (Lattice a, RS a, Eq a) => ResStringConstraint a -> ResStringConstraint a -> Bool
lValidResCon (ResStringConstraint s1 p1) (ResStringConstraint s2 p2)
    = within s1 s2 && lValidPA p1 p2



lValidPA :: (Lattice a, RS a, Eq a) => a -> a -> Bool
lValidPA x y
    = if x == top || y == top
        then True
        else and (map (flip elem (getString x)) (getString y))


lUpdateResCon :: (IC t, Lattice t1, RS t1, Eq t1) =>
                 ResStringConstraint t t1
                 -> ResStringConstraint t t1
                 -> ResStringConstraint t t1
lUpdateResCon (ResStringConstraint s1 p1) (ResStringConstraint s2 p2)
     = ResStringConstraint (serialCombine s1 s2) (lUpdatePA p1 p2)



lUpdatePA :: (Lattice a, RS a, Eq a) => a -> a -> a
lUpdatePA x y
    = if x == bottom || y == bottom
        then bottom
        else y

lSerialApplyLast :: (Eq t1,
                     Eq t,
                     Show t,
                     Lattice t1,
                     Lattice t,
                     IC t,
                     RS t1) =>
                     ExtResStringConstraint t t1 -> ESS t1 -> Either String (ExtResStringConstraint t t1)
lSerialApplyLast x c = lLastApply x (lResEffCons c 0)

lSerialApplyLastBS ::(Eq t,
                     Show t,
                     Lattice t,
                     IC t) =>
                     ExtBS t -> ESS BitString -> Either String (ExtBS t)
lSerialApplyLastBS x c = lLastApplyBS x (lBSEffCons c)


lLastApply :: (Eq t1,
               RS t1,
               Lattice t1,
               IC t,
               Lattice t,
               Eq t,
               Show t) =>
               ExtResStringConstraint t t1 -> Either String (ExtResStringConstraint t t1)
               -> Either String (ExtResStringConstraint t t1)
lLastApply (ExtResStringConstraint r1 _ _) m
    = do
         let foobar
                 = do
                    x@(ExtResStringConstraint r2 e2 _) <- m
                    let foobar1
                         | not (extensible x) = lEitherApply x m
                         | lValidResCon r1 r2 && lValidResCon r1 e2
                            = return (ExtResStringConstraint (lUpdateResCon r1 r2)
                                                    (lUpdateResCon r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
         foobar

lLastApplyBS ::(IC t,
               Lattice t,
               Eq t,
               Show t) =>
               ExtBS t -> Either String (ExtBS t)
               -> Either String (ExtBSt)
lLastApplyBS (ExtBS r1 _ _) m
    = do
         let foobar
                 = do
                    x@(ExtBS r2 e2 _) <- m
                    let foobar1
                         | not (extensible x) = lEitherApplyBS x m
                         | within r1 r2 && within r1 e2
                            = return (ExtBS (serialCombine r1 r2)
                                                    (serialCombine r1 e2) True)
                         | otherwise = throwError "Parent type and constraint mismatch"
                    foobar1
         foobar



\end{code}

resEffCons generates the effective constraint of a restricted
type constraint.

\begin{code}

lResEffCons :: (RS t,
                IC i,
                Lattice i,
                Lattice t,
                Eq i,
                Show i,
                Eq t) =>
                ESS t -> Int ->  Either String (ExtResStringConstraint i t)
lResEffCons (RE c) n        = lResCon c False n
lResEffCons (EXT c) n       = lResCon c True n
lResEffCons (EXTWITH c e) n = lExtendResC (lResCon c False n) (lResCon e False n)

lBSEffCons :: (IC i,
               Lattice i,
               Eq i,
               Show i) =>
                ESS BitString -> Int ->  Either String (ExtBS i)
lBSEffCons (RE c) n        = lBSCon c False n
lBSEffCons (EXT c) n       = lBSCon c True n
lBSEffCons (EXTWITH c e) n = lExtendBSC (lBSCon c False n) (lResCon e False n)
\end{code}

resCon processes constraints. Its second input indicates if the
type is extensible.

\begin{code}

lResCon :: (Eq a,
            Eq i,
            Show i,
            Lattice a,
            Lattice i,
            IC i,
            RS a) =>
            Constr a -> Bool -> Int -> Either String (ExtResStringConstraint i a)
lResCon (UNION u) b n        = lResConU u b n
lResCon (ALL (EXCEPT e)) b n = lResExceptAll top (conE e b n)

lBSCon :: (Eq i,
           Show i,
           Lattice i,
           IC i) =>
            Constr BitString -> Bool -> Int -> Either String (ExtBS i)
lBSCon (UNION u) b n        = lBSConU u b n
lBSCon (ALL (EXCEPT e)) b n = lBSExceptAll top (bsConE e b n)
\end{code}

extendresC implements the extension operator (...) on visiblestring
constraints.
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)

\begin{code}

lExtendResC :: (Eq t,
                Eq t1,
                Lattice t,
                Lattice t1,
                IC t,
                RS t1) =>
                Either String (ExtResStringConstraint t t1)
                -> Either String (ExtResStringConstraint t t1)
                -> Either String (ExtResStringConstraint t t1)
lExtendResC m n
    = do
        let foobar
                = do
                    x@(ExtResStringConstraint r1 e1 _) <- m
                    y@(ExtResStringConstraint r2 e2 _) <- n
                    let foobar1
                            | not (extensible x) && not (extensible y)
                                = return (ExtResStringConstraint r1 (exceptRSC r2 r1) True)
                            | extensible x && not (extensible y)
                                = return (ExtResStringConstraint r1 (exceptRSC (e1 `ljoin` r2) r1) True)
                            | not (extensible x) && extensible y
                                = return (ExtResStringConstraint r1 (exceptRSC (r2 `ljoin` e2) r1) True)
                            | extensible x && extensible y
                                = return (ExtResStringConstraint r1
                                            (exceptRSC (e1 `ljoin` (r2 `ljoin` e2)) r1) True)
                    foobar1
        catchError foobar (\err -> throwError "Invisible")


lExtendBS :: (Eq t,
                Lattice t,
                IC t) =>
                Either String (ExtBS t)
                -> Either String (ExtBS t)
                -> Either String (ExtBS t)
lExtendBS m n
    = do
        let foobar
                = do
                    x@(ExtBS r1 e1 _) <- m
                    y@(ExtBS r2 e2 _) <- n
                    let foobar1
                            | not (extensible x) && not (extensible y)
                                = return (ExtBS r1 (exceptBS r2 r1) True)
                            | extensible x && not (extensible y)
                                = return (ExtBS r1 (exceptBS (e1 `ljoin` r2) r1) True)
                            | not (extensible x) && extensible y
                                = return (ExtBS r1 (exceptBS (r2 `ljoin` e2) r1) True)
                            | extensible x && extensible y
                                = return (ExtBS r1
                                            (exceptBS (e1 `ljoin` (r2 `ljoin` e2)) r1) True)
                    foobar1
        catchError foobar (\err -> throwError "Invisible")
\end{code}

resExceptAll has to deal with the various potential universal
sets which are dependent on the nature of the excepted constraint.
Note: The resulting constraint is non-extensible (see X.680
G.4.3.8)

\begin{code}

lResExceptAll :: (IC i,
                  Eq i,
                  Eq a,
                  RS a,
                  Lattice i,
                  Lattice a) =>
                  ResStringConstraint i a -> Either String (ExtResStringConstraint i a)
                  -> Either String (ExtResStringConstraint i a)
lResExceptAll t m
    = do
         let foobar
                = do
                    ersc <- m
                    let rc = getRC ersc
                        emptyConstraint = rc == bottom
                        foobar1
                            | emptyConstraint = return (ExtResStringConstraint t top False)
                            | otherwise = return (ExtResStringConstraint (exceptRSC top rc) top False)
                    foobar1
         catchError foobar (\err -> throwError "Invisible")

lBSExceptAll :: (IC i,
                  Eq i,
                  Lattice i) =>
                  i -> Either String (ExtBS i)
                  -> Either String (ExtBS i)
lBSExceptAll t m
    = do
         let foobar
                = do
                    ersc <- m
                    let rc = getBSRC ersc
                        emptyConstraint = rc == bottom
                        foobar1
                            | emptyConstraint = return (ExtBS t top False)
                            | otherwise = return (ExtBS (exceptBS top rc) top False)
                    foobar1
         catchError foobar (\err -> throwError "Invisible")


lResConU :: (RS t,
             IC i,
             Lattice i,
             Lattice t,
             Eq i,
             Show i,
             Eq t) =>
             Union t -> Bool -> Int -> Either String (ExtResStringConstraint i t)
lResConU (IC i) b  n  = lResConI i b n
lResConU (UC u i) b n = lUnionResC (lResConI i b n) (lResConU u False n)


lBSConU :: (IC i,
            Lattice i,
            Eq i,
            Show i) =>
            Union BitString -> Bool -> Int -> Either String (ExtBS i)
lBSConU (IC i) b  n  = lBSConI i b n
lBSConU (UC u i) b n = lUnionBS (lBSConI i b n) (lBSConU u False n)

\end{code}

unionRes returns the union of two pairs of constraints. Note
that the union of a size constraint (and no permitted alphabet constraint)
and vice versa result in no constraint.
sizeUnion and paUnion union size and permitted alphabet constraints respectively.

unionresC implements the union operator on visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680) Note that a union of a size constraint and a permitted
alphabet constraint is an unconstrained type.

\begin{code}

lUnionResC :: (IC i,
               Eq i,
               Eq a,
               RS a,
               Lattice i,
               Lattice a) =>
               Either String (ExtResStringConstraint i a)
               -> Either String (ExtResStringConstraint i a)
               -> Either String (ExtResStringConstraint i a)
lUnionResC m n
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
                        | not (extensible c1) && not (extensible c2)
                             = return (ExtResStringConstraint (r1 `ljoin` r2) top False)
                        | not (extensible c1)
                             = return (ExtResStringConstraint (r1 `ljoin` r2) e2 True)
                        | extensible c1 && not (extensible c2)
                             = return (ExtResStringConstraint (r1 `ljoin` r2) e1 True)
                        | otherwise
                             = return (ExtResStringConstraint (r1 `ljoin` r2)
                                       (exceptRSC ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2))
                                                  (r1 `ljoin` r2)) True)
                foobar1
        catchError foobar (\err -> throwError "Invisible")

lUnionBS :: (IC i,
             Eq i,
             Lattice i) =>
             Either String (ExtBS i)
             -> Either String (ExtBS i)
             -> Either String (ExtBS i)
lUnionBS m n
    = do
        let foobar
             = do
                c1 <- m
                c2 <- n
                let r1 = getBSRC c1
                    e1 = getBSEC c1
                    r2 = getBSRC c2
                    e2 = getBSEC c2
                    foobar1
                        | not (extensible c1) && not (extensible c2)
                             = return (ExtBS (r1 `ljoin` r2) top False)
                        | not (extensible c1)
                             = return (ExtBS (r1 `ljoin` r2) e2 True)
                        | extensible c1 && not (extensible c2)
                             = return (ExtBS (r1 `ljoin` r2) e1 True)
                        | otherwise
                             = return (ExtBS (r1 `ljoin` r2)
                                       (exceptBS ((r1 `ljoin` e1) `ljoin` (r2 `ljoin` e2))
                                                  (r1 `ljoin` r2)) True)
                foobar1
        catchError foobar (\err -> throwError "Invisible")



\end{code}

resConI deals with the intersection of visiblestring constraints

\begin{code}

lResConI :: (Eq t,
             Eq i,
             Show i,
             Lattice t,
             Lattice i,
             IC i,
             RS t) =>
             IntCon t -> Bool -> Int -> Either String (ExtResStringConstraint i t)
lResConI (INTER i e) b n = lInterResC (lResConA e b n) (lResConI i False n)
lResConI (ATOM e) b n    = lResConA e b n


lBSConI :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            IntCon BitString -> Bool -> Int -> Either String (ExtBS i t)
lBSConI (INTER i e) b n = lInterBSC (lBSConA e b n) (lBSConI i False n)
lBSConI (ATOM e) b n    = lBSConA e b n
\end{code}

interResC implements the intersection of visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lInterResC :: (Eq i,
               Eq a,
               Lattice i,
               Lattice a,
               IC i,
               RS a) =>
               Either String (ExtResStringConstraint i a)
               -> Either String (ExtResStringConstraint i a)
               -> Either String (ExtResStringConstraint i a)
lInterResC m n
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
                            | not (extensible c1) && not (extensible c2)
                                 = return (ExtResStringConstraint (r1 `meet` r2) top False)
                            | not (extensible c1)
                                 = return (ExtResStringConstraint (r1 `meet` r2) (r1 `meet` e2) True)
                            | extensible c1 && not (extensible c2)
                                 = return (ExtResStringConstraint (r1 `meet` r2) (r2 `meet` e1)  True)
                            | otherwise
                                 = return (ExtResStringConstraint (r1 `meet` r2) (exceptRSC ((r1 `ljoin` e1)
                                        `meet` (r2 `ljoin` e2)) (r1 `meet` r2)) True)
                    foobar3
             foobar
                = catchError (do c1 <- m
                                 foobar1 c1)
                             (\err -> n)
         foobar


lInterBS :: (Eq i,
              Lattice i,
              IC i) =>
              Either String (ExtBS i)
              -> Either String (ExtBS i)
              -> Either String (ExtBS i)
lInterBS m n
    = do
         let foobar1 x
                 = do catchError (do c2 <- n
                                     foobar2 x c2)
                                 (\err -> m)
             foobar2 c1 c2
                 = do
                    let r1 = getBSRC c1
                        e1 = getBSEC c1
                        r2 = getBSRC c2
                        e2 = getBSEC c2
                        foobar3
                            | not (extensible c1) && not (extensible c2)
                                 = return (ExtBS (r1 `meet` r2) top False)
                            | not (extensible c1)
                                 = return (ExtBS (r1 `meet` r2) (r1 `meet` e2) True)
                            | extensible c1 && not (extensible c2)
                                 = return (ExtBS (r1 `meet` r2) (r2 `meet` e1)  True)
                            | otherwise
                                 = return (ExtBS (r1 `meet` r2) (exceptBS ((r1 `ljoin` e1)
                                        `meet` (r2 `ljoin` e2)) (r1 `meet` r2)) True)
                    foobar3
             foobar
                = catchError (do c1 <- m
                                 foobar1 c1)
                             (\err -> n)
         foobar

\end{code}

resConA deals with atomic (including except) constraints

\begin{code}

lResConA :: (Eq t,
             Eq i,
             Show i,
             Lattice t,
             Lattice i,
             IC i,
             RS t) =>
             IE t -> Bool -> Int -> Either String (ExtResStringConstraint i t)
lResConA (E e) b n = conE e b n
lResConA (Exc e (EXCEPT ex)) b n
                = lExceptResC (conE e b n) (conE ex False n)


lBSConA :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            IE BitString -> Bool -> Int -> Either String (ExtBS i)
lBSConA (E e) b n = conE e b n
lBSConA (Exc e (EXCEPT ex)) b n
                = lExceptBS (lBSConE e b) (lBSConE ex False)
\end{code}

resExcept implements the set difference operator applied to
visiblestring constraints
Needs to satisfy the rules regarding visibility (see Annex B.2.2.10 of X.691)
and set operators and effective constraints (see G.4.3.8 of
X.680)

\begin{code}

lExceptResC :: (IC i,
                Eq i,
                Eq a,
                RS a,
                Lattice i,
                Lattice a) =>
                Either String (ExtResStringConstraint i a)
                -> Either String (ExtResStringConstraint i a)
                -> Either String (ExtResStringConstraint i a)
lExceptResC m n
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
                            | not (extensible c1)
                                = return (ExtResStringConstraint (exceptRSC r1 r2) top False)
                            | extensible c1 && not (extensible c2)
                                 = return (ExtResStringConstraint (exceptRSC r1 r2)
                                            (exceptRSC (exceptRSC r1 e2) (exceptRSC r1 r2)) True)
                            | otherwise
                                 = return (ExtResStringConstraint (exceptRSC r1 r2)
                                            (exceptRSC (exceptRSC r1 (r2 `ljoin` e2))
                                                       (exceptRSC r1 r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> throwError "Invisible")
         foobar


lExceptBS :: (IC i,
              Eq i,
              Lattice i) =>
              Either String (ExtBS i)
                -> Either String (ExtBS i)
                -> Either String (ExtBS i)
lExceptResC m n
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
                            | not (extensible c1)
                                = return (ExtBS (exceptBS r1 r2) top False)
                            | extensible c1 && not (extensible c2)
                                 = return (ExtBS (exceptBS r1 r2)
                                            (exceptBS (exceptBS r1 e2) (exceptBS r1 r2)) True)
                            | otherwise
                                 = return (ExtBS (exceptBS r1 r2)
                                            (exceptBS (exceptBS r1 (r2 `ljoin` e2))
                                                       (exceptBS r1 r2)) True)
                    foobar3
             foobar
                = catchError (do
                               c1 <- m
                               foobar1 c1)
                             (\err -> throwError "Invisible")
         foobar

\end{code}

resConE deals with the various visiblestring constraints
Note that a permitted alphabet constraint uses value range
constraint(s) and that extensible permitted alphabet
constraints are not per-visible.
The first case (size-constraint) we can make use of the
functions that create an effective Integer constraint. We
cannot use evalC since it includes serial application of
constraints.

\begin{code}

conE e b n
    | n == 0 = lResConE e b
    | otherwise = lPaConE e b

lResConE :: (Eq a,
             Eq i,
             Show i,
             Lattice a,
             Lattice i,
             IC i,
             RS a) =>
             Elem a -> Bool -> Either String (ExtResStringConstraint i a)
lResConE (SZ (SC v)) b            = lEffResSize v b
lResConE (P (FR (EXT _))) b       = throwError "Invisible!"
lResConE (P (FR (EXTWITH _ _))) b = throwError "Invisible!"
lResConE (P (FR (RE p)))  b       = lResEffCons (RE p) 1
lResConE (C (Inc c)) b            = lProcessCST c []
lResConE (S (SV v))  b            = throwError "Invisible!"


lBSConE :: (Eq i,
            Show i,
            Lattice i,
            IC i) =>
            Elem BitString -> Bool -> Either String (ExtBS i)
lBSConE (SZ (SC v)) b  = lEffBSSize v b
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
            Lattice a1,
            RS a,
            Eq a,
            Eq a1,
            Show a1,
            IC a1) =>
            Elem a -> Bool -> Either String (ExtResStringConstraint a1 a)
lPaConE (V (R (l,u))) b
    = let ls = getString l
          us = getString u
          rs = [head ls..head us]
        in
            return (ExtResStringConstraint (ResStringConstraint top (makeString rs))
                        (ResStringConstraint top top) b)
lPaConE (C (Inc c)) b = lProcessCST c []
lPaConE (S (SV v)) b
   = return (ExtResStringConstraint (ResStringConstraint top v)
                                      (ResStringConstraint top top) b)


lEffResSize :: (IC t,
                Lattice a,
                Lattice t,
                RS a,
                Eq a,
                Eq t,
                Show t) =>
                ESS InfInteger -> Bool -> Either String (ExtResStringConstraint t a)
lEffResSize (RE c) b
    = do ec <- lCalcC c
         return (ExtResStringConstraint (ResStringConstraint ec top) top b)
lEffResSize (EXT c) b
    = do ec <- lCalcC c
         return (ExtResStringConstraint (ResStringConstraint ec top) top True)
lEffResSize (EXTWITH c d) b
    = do r <- lCalcC c
         e <- lCalcC d
         return (ExtResStringConstraint (ResStringConstraint r top)
                                        (ResStringConstraint e top)  True)


lEffBSSize :: (IC t,
               Lattice t,
               Eq t,
               Show t) =>
               ESS InfInteger -> Bool -> Either String (ExtBS t)
lEffBSSize (RE c) b
    = do ec <- lCalcC c
         return (ExtBS ec top b)
lEffBSSize (EXT c) b
    = do ec <- lCalcC c
         return (ExtBS ec top True)
lEffBSSize (EXTWITH c d) b
    = do r <- lCalcC c
         e <- lCalcC d
         return (ExtBS r e True)

lProcessCST :: (Eq a,
                Eq i,
                Show i,
                Lattice a,
                Lattice i,
                IC i,
                RS a) => ASNType a -> [ESS a] -> Either String (ExtResStringConstraint i a)
lProcessCST (BT _) cl = lRootStringCons top cl
lProcessCST (ConsT t c) cl = lProcessCST t (c:cl)


lRootStringCons t cs
    = let m = lSerialResEffCons t cs
      in do
            (ExtResStringConstraint r e _) <- m
            return (ExtResStringConstraint r top False)

\end{code}
