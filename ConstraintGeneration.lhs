\begin{code}
{-# OPTIONS_GHC -XTypeOperators -XGADTs -XEmptyDataDecls
                -XFlexibleInstances -XFlexibleContexts
#-}
module ConstraintGeneration where

import ASNTYPE
import LatticeMod
import Control.Monad.Error
\end{code}

This module provides the functions that convert a list of subtype constraints -- the Haskell
list type is used to represent zero or more serially applied constraints -- into a single
effective constraint and a single actual constraint. A type's effective constraint is used to
PER-encode a value of the type. The actual constraint is used to test the validity of a value.
Note that only PER-visible constraints are used in the generation of an effective constraint
(X.691: 9.3.18) but all constraints are used in the generation of an actual constraint.

{\em generateConstraint} takes a list of constraints (representing
serially applied constraints) and generates the resulting constraint (if it exists).
It is a recursive function which takes three inputs:
\begin{\itemize}
\item
a type-specific function that processes the element constraints appropriately for the given
type and whether one is generating an effective constraint or a validity-testing constraint.
Thus when one is generating an effective constraint an error will be thrown if the constraint
is non-PER visible;
\item
an accumulation parameter which presents the current status of the constraint; and
\item
the list of serially-applied constraints to be processed.
\end{itemize}

The function has three cases:
\begin{itemize}
\item
the empty list of constraints where no further constraints need to be processed and the
accumulated value is simply returned;
\item
the singleton list of constraints which represents the last constraint to be processed. This
is managed by the function {\em applyLastConstraint}. Note that the serial application of the last constraint
is semantically different from the others in that the extensibility of the resulting constraint depends only on the
last constraint (X.680: G.4.2.3); and
\item
a list of at least two constraints where the accumulating parameter is updated using {\em
applyConstraint} and {\em generateConstraint} is recursively called with the result of {\em applyConstraint}
as the second input.
\end{itemize}

\begin{code}

generateConstraint :: (MonadError [Char] t,
                      ExtConstraint a1,
                      Eq (b i),
                      ConstructedConstraint b i,
                      Lattice (b i),
                      ExtConstraint a) =>
                     (Element t1 -> Bool -> t (a (b i))) -> t (a1 (b i))
                        -> [SubtypeConstraint t1] -> t (a1 (b i))
generateConstraint fn m ls
    = do
        let foobar
                = do
                    esrc <- m
                    let foobar1 [] = m
                        foobar1 [c] = applyLastConstraint fn esrc c
                        foobar1 (f:r) = generateConstraint fn (applyConstraint fn esrc f) r
                    foobar1 ls
        foobar

\end{code}

{\em applyConstraint} takes the same first two inputs as {\em generateConstraint} and the next constraint to be serially applied.
It calls {\em makeConstraint} which, if the new constraint is valid then it is serially applied, and, if not, the function
{\em constraintApplicationError} is called whose behaviour depends on the type of error.


\begin{code}

applyConstraint :: (Eq (b i),
                 ConstructedConstraint b i,
                 Lattice (b i),
                 ExtConstraint a1,
                 MonadError [Char] m,
                 ExtConstraint a) =>
                (Element t -> Bool -> m (a1 (b i)))
                -> a (b i)
                -> SubtypeConstraint t
                -> m (a (b i))
applyConstraint fn ersc c
    = catchError (makeConstraint ersc (generateSingleConstraint False fn c)) (constraintApplicationError ersc)

\end{code}

{\em makeConstraint} simply accesses the root constraints of the current constraint (represented by the accumulating
parameter)and the new constraint, and if the new constraint is valid it updates the accumulated constraint using the
function {\em makeExtensibleConstraint}. {\em makeExtensibleConstraint} is a method of the type class {\em ExtConstraint}
defined in the module {\em LatticeMod} and is thus supported by all extensible constraints. Note that
{\em makeExtensibleConstraint} simply updates the root constraint using {\em updateConstraint} which is a method of the type
class {\em Constraint} also defined in {\em LatticeMod}. The extension becomes {\em top}
-- all possible values -- which indicates no constraint since the serial application of a constraint removes the extension
from the existing constraint (X.680: G.4.2.3). Note however, that the validity tests requires
that both the root and extension of the serially applied constraint only contain values from the
root of the parent constraint (X680: G.4.2.3).

The function {\em constraintApplicationError} results in the second constraint being ignored
if the error reported indicates a non-PER visible constraint (X.691: B.2.2.2), and passes the error on
otherwise. That is, any non-visibility error results in no constraint being generated.

\begin{code}

makeConstraint :: (MonadError [Char] m,
                 ExtConstraint a,
                 ExtConstraint a1,
                 ConstructedConstraint b i,
                 Lattice (b i),
                 ExtConstraint a2) =>
                a (b i) -> m (a1 (b i)) -> m (a2 (b i))
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

\end{code}

{\em applyLastConstraint} is similar to {\em applyConstraint} except that if the last
constraint is extensible and valid then the generated constraint is extensible. The function
{\em makeFinalConstraint} generates the final constraint.

\begin{code}

applyLastConstraint :: (Eq (b i),
                     ConstructedConstraint b i,
                     Lattice (b i),
                     ExtConstraint a1,
                     MonadError [Char] m,
                     ExtConstraint a) =>
                    (Element t -> Bool -> m (a1 (b i)))
                    -> a (b i)
                    -> SubtypeConstraint t
                    -> m (a (b i))
applyLastConstraint fn x c
    = catchError (makeFinalConstraint x (generateSingleConstraint False fn c)) (constraintApplicationError x)


makeFinalConstraint :: (MonadError [Char] t,
               ExtConstraint a1,
               ExtConstraint a2,
               Lattice (b i),
               ConstructedConstraint b i,
               ExtConstraint a) =>
              a (b i) -> t (a1 (b i)) -> t (a2 (b i))
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

\end{code}

{\em generateSingleConstraint} generates a single constraint which is then used in the serial
application of constraints. Its construction is guided by the structure of a {\tt SubtypeConstraint} as presented
in section 46 of X.680. {\em generateSingleConstraint} takes three inputs:
\begin{itemize}
\item
a boolean value which indicates whether the constraint is extensible;
\item
the type-specific function that appropriately processes an element constraint; and
\item
a subtype constraint which has the three cases specified at the top level of {\tt ElementSetSpecs}:
a non-extensible constraint indicated by the
constructor {\em RootOnly}, an extensible constraint with no extension additions indicated by
the constructor {\em EmptyExtension} and an extensible constraint with an extension addition
indicated by the constructor {\em NonEmptyExtension}.
\end{itemize}

The rules for generating a (possibly extensible) constraint using set arithmetic are presented
in X.680: G.4.3.8. The rules include a description of how to generate a constraint from an
extensible constraint whose root and extension addition may themselves be extensible. The
function {\em extensibleConstraint} implements these rules and the other set operations are
implemented by {\em applySetOperations}.

\begin{code}

generateSingleConstraint :: (Eq (b i),
                ConstructedConstraint b i,
                Lattice (b i),
                ExtConstraint a,
                MonadError [Char] t1) => Bool ->
               (Element t -> Bool -> t1 (a (b i))) -> SubtypeConstraint t -> t1 (a (b i))
generateSingleConstraint x fn (RootOnly c)              = applySetOperations fn c x
generateSingleConstraint _ fn (EmptyExtension c)        = applySetOperations fn c True
generateSingleConstraint _ fn (NonEmptyExtension c e)
        = extensibleConstraint (applySetOperations fn c False) (applySetOperations fn e False)

\end{code}

{\em applySetOperations} implements the top-level of the set operations. That is, a constraint
is either the union of constaints indicated by the constructor {\em UnionSet} or the
complement set of a set of excluded values as indicated by the constructor {\em
ComplementSet}.

\begin{code}

applySetOperations :: (MonadError [Char] t1,
            ExtConstraint a,
            Lattice (b i),
            ConstructedConstraint b i,
            Eq (b i)) =>
           (Element t -> Bool -> t1 (a (b i))) -> ElementSetSpec t -> Bool -> t1 (a (b i))
applySetOperations fn (UnionSet u) b                = applyUnions fn u b
applySetOperations fn (ComplementSet (EXCEPT e)) b  = applyExceptAll (fn e b)

\end{code}

{\em extensibleConstraint} implements the rules for an extension operator (...).
Note that it needs to satisfy the rules regarding PER-visibility (X.691: B.2.2.10). That is,
if either the root or extension component are non-PER visible then the overall constraint is
non-PER visible. Note that {\em ljoin} is the lattice join operator defined in the type class
{\em Lattice} in the module {\em LatticeMod}.

\begin{code}

extensibleConstraint :: (MonadError [Char] m,
                Lattice (b i),
                ExtConstraint a2,
                ConstructedConstraint b i,
                ExtConstraint a1,
                ExtConstraint a) =>
               m (a1 (b i)) -> m (a (b i)) -> m (a2 (b i))
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

\end{code}

{\em applyExceptAll} generates an {\tt ALL Exclusions} constraint. If the excluded set is
empty then there is no constraint and thus {\em top} is returned. Otherwise
the complement set of the excluded set is returned. Note that since the constraint
representing {\tt ALL} is non-extensible -- all the values are in the root -- the resulting
constraint is non-extensible by the rule described in X.680: G.4.3.8. Note also that if the
constraint representing the excluded values is non-PER visible then it is ignored and the
resulting constraint is everything.

\begin{code}

applyExceptAll :: (MonadError [Char] m,
                  ConstructedConstraint b i,
                  ExtConstraint a1,
                  Eq (b i),
                  Lattice (b i),
                  ExtConstraint a) =>
                 m (a (b i)) -> m (a1 (b i))
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

\end{code}

{\em applyUnions} generates a {\tt Unions} constraint. It has two cases:
\begin{itemize}
\item
the case when there is no union operator as undicated by the constructor {\em NoUnion}; and
\item
the case where there is at least one union as indicated by the constructor {\em UnionMark}.
\end{itemize}

\begin{code}

applyUnions :: (ConstructedConstraint b i,
             Lattice (b i),
             ExtConstraint a,
             MonadError [Char] t1) =>
            (Element t -> Bool -> t1 (a (b i))) -> Unions t -> Bool -> t1 (a (b i))
applyUnions fn (NoUnion i) b     = applyIntersections fn i b
applyUnions fn (UnionMark u i) b = unionConstraints (applyIntersections fn i b) (applyUnions fn u False)

\end{code}

{\em unionConstraints} returns the union of constraints.
Note that {\em unionConstraints} needs to satisfy the rules regarding visibility -- if either constraint
is non-PER visible then the union is non-PER visible (X.691: B.2.2.10) --
and set operators and effective constraints (X.680: G.4.3.8) Note also that the union of a size constraint and a permitted
alphabet constraint is no constraint which is represent by the lattice value {\em top}.

\begin{code}

unionConstraints :: (MonadError [Char] m,
               ConstructedConstraint b i,
               ExtConstraint a2,
               Lattice (b i),
               ExtConstraint a1,
               ExtConstraint a) =>
              m (a1 (b i)) -> m (a (b i)) -> m (a2 (b i))
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

\end{code}

{\em applyIntersections} generates a {\tt Intersections} constraint. It has two cases:
\begin{itemize}
\item
the case when there is no intersection operator as undicated by the constructor {\em NoIntersection}; and
\item
the case where there is at least one intersection as indicated by the constructor {\em IntersectionMark}.
\end{itemize}

\begin{code}

applyIntersections :: (MonadError [Char] t1,
             ExtConstraint a,
             Lattice (b i),
             ConstructedConstraint b i) =>
            (Element t -> Bool -> t1 (a (b i))) -> Intersections t -> Bool -> t1 (a (b i))
applyIntersections fn (NoIntersection e) b    = intersectionElements fn e b
applyIntersections fn (IntersectionMark i e) b
    = intersectionConstraints (intersectionElements fn e b) (applyIntersections fn i False)


\end{code}

{\em intersectionConstraints} returns the intersection of constraints.
Note that {\em intersectionConstraints} needs to satisfy the rules regarding visibility
-- a non-PER visible constraint is simply ignored (X.691: B.2.2.10) --
and set operators and effective constraints (X.680: G.4.3.8).

\begin{code}

intersectionConstraints :: (Lattice (b i),
               ConstructedConstraint b i,
               MonadError e t,
               ExtConstraint a) =>
              t (a (b i)) -> t (a (b i)) -> t (a (b i))
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

\end{code}

{\em intersectionElements} generates a constraint from an {\tt IntersectionElements} value.
There are two possible cases: a simple element constraint indicated by the constructor
{\em ElementConstraint} or an exclusion constraint (the set difference of two constraints)
indicated by the constructor {\em ExclusionConstraint). Note that for the {\em
ElementConstraint} case, the element processing function which was provided as an input to the
top-level function {\em generateConstraint} is now applied to the element constraint. In the
other case the element encoding function is applied to each element constraint and {\em
exceptConstraints} is applied to their results.

\begin{code}

intersectionElements :: (ExtConstraint a,
             MonadError [Char] m,
             Lattice (b i),
             ConstructedConstraint b i) =>
            (Element t -> Bool -> m (a (b i))) -> IntersectionElements t -> Bool -> m (a (b i))
intersectionElements fn (ElementConstraint e) b  = fn e b
intersectionElements fn (ExclusionConstraint e (EXCEPT ex)) b
                = exceptConstraints (fn e b) (fn ex False)

\end{code}

{\em exceptConstraints} returns the set difference of constraints.
Note that {\em exceptConstraints} needs to satisfy the rules regarding visibility
-- a non-PER visible constraint is ignored if it is the exception value but makes the whole
constraint no-PER visible otherwise (X.691: B.2.2.10) --
and set operators and effective constraints (X.680: G.4.3.8).

\begin{code}

exceptConstraints  :: (ConstructedConstraint b i,
                ExtConstraint a,
                Lattice (b i),
                MonadError [Char] m,
                ExtConstraint a1) =>
               m (a1 (b i)) -> m (a (b i)) -> m (a1 (b i))
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

\end{code}

The following functions are the element processing functions for the types with PER-visible
constraints.

{\em pvIntegerElements} processes the various {\tt IntegerType} constraints which are all
PER-visible. Since all constraints are represented as potentially extensible constraints
with the boolean parameter indicating extensible constraint or not, the processing results in
a value of type {\em Either String (ExtensibleConstraint (ConstructConstraint a))}. If a valid constraint
is generated then a {\em ExtensibleConstraint (ConstructConstraint a)} value is returned. The constructor
{\em ConstructConstraint} is used simply to created a constructed constraint value from a simple
constraint such as an {\em IntegerConstraint}.

\begin{code}


pvIntegerElements :: (IntegerCon a, Lattice a, Eq a, Show a)
    => Element InfInteger -> Bool -> Either String (ExtensibleConstraint (ConstructConstraint a))
pvIntegerElements (S (SV i)) b
    = return (makeExtensibleConstraint
                (makeConstructedConstraint $ makeIntegerConstraint i i) top b)
pvIntegerElements (C (Inc t)) b
    = lProcessCT t []
pvIntegerElements (V (R (l,u))) b
    = return (makeExtensibleConstraint
                (makeConstructedConstraint $ makeIntegerConstraint l u) top b)

-- {- FIXME Parent type does not inherit extension of included type -}

lProcessCT :: (IntegerCon a, Lattice a, Eq a, Show a) =>
              ASNType InfInteger -> [SubtypeConstraint InfInteger] -> Either String (ExtensibleConstraint (ConstructConstraint a))
lProcessCT (BuiltinType INTEGER) cl = generateConstraint pvIntegerElements top cl
lProcessCT (ConstrainedType t c) cl  = lProcessCT t (c:cl)

{- FIXME: Note that boolean input is thrown away -}

lResConE :: (RS a,
                IntegerCon i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) =>
                Element a -> Bool ->  Either String (ExtensibleConstraint (ResStringConstraint a i))
lResConE (SZ (SC v)) b            = convertIntToRS $ generateSingleConstraint b pvIntegerElements v
lResConE (P (FR (EmptyExtension _))) b       = throwError "Invisible!"
lResConE (P (FR (NonEmptyExtension _ _))) b = throwError "Invisible!"
lResConE (P (FR (RootOnly p)))  b       = generateSingleConstraint b lPaConE (RootOnly p)
lResConE (C (Inc c)) b            = lProcessCST lResConE c []
lResConE (S (SV v))  b            = throwError "Invisible!"


convertIntToRS :: (RS a,
                IntegerCon i,
                Lattice i,
                Lattice a,
                Eq i,
                Show i,
                Eq a) => Either String (ExtensibleConstraint (ConstructConstraint i))
                         -> Either String (ExtensibleConstraint (ResStringConstraint a i))
convertIntToRS (Right (ExtensibleConstraint (ConstructConstraint x) (ConstructConstraint y) b))
    = Right (ExtensibleConstraint (ResStringConstraint top x) (ResStringConstraint top y) b)
convertIntToRS (Left s) = Left s

{- FIXME: Note that boolean is thrown away -}

lBSConE :: (Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element BitString -> Bool -> Either String (ExtensibleConstraint (ConstructConstraint i))
lBSConE (SZ (SC v)) b  = generateSingleConstraint b pvIntegerElements v
lBSConE (C (Inc c)) b  = throwError "Invisible!"
lBSConE (S (SV v))  b  = throwError "Invisible!"

{- FIXME: Note that boolean input is thrown away -}
lOSConE :: (Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element OctetString -> Bool -> Either String (ExtensibleConstraint (ConstructConstraint i))
lOSConE (SZ (SC v)) b  = generateSingleConstraint b pvIntegerElements v
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
            IntegerCon i) =>
            Element a -> Bool -> Either String (ExtensibleConstraint (ResStringConstraint a i))
lPaConE (V (R (l,u))) b
    = let ls = getString l
          us = getString u
          rs = [head ls..head us]
        in
            return (ExtensibleConstraint (ResStringConstraint (makeString rs) bottom)
                        (ResStringConstraint top top) b)
lPaConE (C (Inc c)) b = lProcessCST lPaConE c []
lPaConE (S (SV v)) b
   = return (ExtensibleConstraint (ResStringConstraint v top)
                                      (ResStringConstraint top top) b)

{- FIXME: Note that boolean value is thrown away -}

lSeqOfConE :: (Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element [a] -> Bool -> Either String (ExtensibleConstraint (ConstructConstraint i))
lSeqOfConE (SZ (SC v)) b  = generateSingleConstraint b pvIntegerElements v
lSeqOfConE (C (Inc c)) b  = throwError "Invisible!"
lSeqOfConE (S (SV v))  b  = throwError "Invisible!"
lSeqOfConE (IT (WC c)) b  = throwError "Invisible!"
lSeqOfConE (IT WCS) b     = throwError "Invisible!"






lProcessCST :: (Lattice (t1 (a1 (b i))),
                MonadError [Char] t1,
                ExtConstraint a1,
                Eq (b i),
                ConstructedConstraint b i,
                Lattice (b i)) =>
               (Element t -> Bool -> t1 (a1 (b i))) -> ASNType t -> [SubtypeConstraint t] -> t1 (a1 (b i))
lProcessCST fn (BuiltinType _) cl = lRootStringCons fn top cl
lProcessCST fn (ConstrainedType t c) cl = lProcessCST fn t (c:cl)


lRootStringCons :: (ExtConstraint a,
                    Lattice (b i),
                    ConstructedConstraint b i,
                    Eq (b i),
                    MonadError [Char] t1) =>
                   (Element t -> Bool -> t1 (a (b i))) -> t1 (a (b i)) -> [SubtypeConstraint t] -> t1 (a (b i))
lRootStringCons fn t cs
    = let m = generateConstraint fn t cs
      in do
            c <- m
            r <- return (getRootConstraint c)
            return (makeExtensibleConstraint r top False)

\end{code}

A useful function:

\begin{code}

rangeConstraint :: (ValueRange a) => (a, a) -> SubtypeConstraint a
rangeConstraint =  RootOnly . UnionSet . IC . ATOM . E . V . R

\end{code}