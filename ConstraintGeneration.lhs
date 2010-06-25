\section{Constraint Generating Functions}

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
We first present in section \ref{congen} the non-type specific functions used in constraint generation. This is followed in section \ref{contype}
with the type-specific functions that process the element constraints of each type.

\subsection{Non-Type Specific Constraint Generation Functions}
\label{congen}

{\em evaluateConstraint} takes a list of constraints (representing
serially applied constraints) and returns the resulting constraint (if it exists). It is used to evaluate
both the effective constraint and the validity-testing constraint.
It is a recursive function which takes three inputs:
\begin{\itemize}
\item
a type-specific function that processes the element constraints appropriately for the given
type. That is, each type has a collection of applicable constraints as presented in table 9 of
section 47.1 of X.680. The function used depends on whether one is generating an effective constraint -- in which
case some of the elements are non-PER visible -- or a validity-testing constraint where all valid constraints
are visible. When one is generating an effective constraint an error will be thrown if the constraint
is non-PER visible;
\item
an accumulation parameter which presents the current status of the constraint. That is, as the serially-applied
constraints are evaluated they are serially-applied to the constraint hosted by this parameter. We will refer to
this constraint as the {\bf parent constraint}; and
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
applyConstraint} and {\em evaluateConstraint} is recursively called with the result of {\em applyConstraint}
as the second input.
\end{itemize}

\begin{code}

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

\end{code}

{\em applyConstraint} takes the same first two inputs as {\em evaluateConstraint} and the next constraint to be serially applied.
It uses {\tt evaluateSingleConstraint} to create a single constraint from a constraint which is potentially defined using set operations,
and applies {\em makeConstraint} to the parent constraint and the newly evaluated constraint. If the new
constraint is valid -- its values lie within the root of the parent constraint -- then it is serially applied, and, if not, the function
{\em constraintApplicationError} is called whose behaviour depends on the type of error.


\begin{code}

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

\end{code}

{\em makeConstraint} simply accesses the root constraints of the parent constraint and the new constraint, and if the new constraint is valid it
updates the parent constraint using the
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
otherwise. That is, any non-visibility error results in no constraint being evaluated.

\begin{code}

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

\end{code}

{\em applyLastConstraint} is similar to {\em applyConstraint} except that if the last
constraint is extensible and valid then the evaluated constraint is extensible. The function
{\em makeFinalConstraint} evaluates the final constraint.

\begin{code}

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

\end{code}

{\em evaluateSingleConstraint} evaluates a single constraint which is then used in the serial
application of constraints. Its construction is guided by the structure of a {\tt SubtypeConstraint} as presented
in section 46 of X.680. {\em evaluateSingleConstraint} takes three inputs:
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

The rules for evaluating a (possibly extensible) constraint using set arithmetic are presented
in X.680: G.4.3.8. The rules include a description of how to evaluate a constraint from an
extensible constraint whose root and extension addition may themselves be extensible. The
function {\em extensibleConstraint} implements these rules and the other set operations are
implemented by {\em applySetOperations}.

\begin{code}

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

\end{code}

{\em applySetOperations} implements the top-level of the set operations. That is, a constraint
is either the union of constaints indicated by the constructor {\em UnionSet} or the
complement set of a set of excluded values as indicated by the constructor {\em
ComplementSet}.

\begin{code}

applySetOperations :: (MonadError [Char] t1,
            ExtConstraint a,
            Lattice c,
            Constraint c,
            Eq c) =>
           (Element t -> Bool -> t1 (a c)) -> ElementSetSpec t -> Bool -> t1 (a c)
applySetOperations fn (UnionSet u) b                = applyUnions fn u b
applySetOperations fn (ComplementSet (EXCEPT e)) b  = applyExceptAll (fn e b)

\end{code}

{\em extensibleConstraint} implements the rules for an extension operator (...).
Note that when generating the effective constraint it needs to satisfy the rules regarding PER-visibility (X.691: B.2.2.10). That is,
if either the root or extension component are non-PER visible then the overall constraint is
non-PER visible. {\em ljoin} is the lattice join operator defined in the type class
{\em Lattice} in the module {\em LatticeMod}.

Note also that the only error that may be thrown is a non-PER-visible error. Haskell's type system will deal with any attempt
to use an inapplicable constraint, and non-valid constraints are dealt with during serial application.

\begin{code}

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

\end{code}

{\em applyExceptAll} evaluates an {\tt ALL Exclusions} constraint. If the excluded set is
empty then there is no constraint and thus {\em top} is returned. Otherwise
the complement set of the excluded set is returned. Note that since the constraint
representing {\tt ALL} is non-extensible -- all the values are in the root -- the resulting
constraint is non-extensible by the rule described in X.680: G.4.3.8. Hence the last input to
{\tt makeExtensibleConstraint} is {\tt False}. Note also that if the
constraint representing the excluded values is non-PER visible then, by X691: B.2.2.10,  it is ignored
and the resulting constraint is everything.

\begin{code}

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

\end{code}

{\em applyUnions} evaluates a {\tt Unions} constraint. It has two cases:
\begin{itemize}
\item
the case when there is no union operator as indicated by the constructor {\em NoUnion}; and
\item
the case where there is at least one union as indicated by the constructor {\em UnionMark}.
\end{itemize}

\begin{code}

applyUnions :: (Constraint c,
             Lattice c,
             ExtConstraint a,
             MonadError [Char] t1) =>
            (Element t -> Bool -> t1 (a c)) -> Unions t -> Bool -> t1 (a c)
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

\end{code}

{\em applyIntersections} evaluates a {\tt Intersections} constraint. It has two cases:
\begin{itemize}
\item
the case when there is no intersection operator as undicated by the constructor {\em NoIntersection}; and
\item
the case where there is at least one intersection as indicated by the constructor {\em IntersectionMark}.
\end{itemize}

\begin{code}

applyIntersections :: (MonadError [Char] t1,
             ExtConstraint a,
             Lattice c,
             Constraint c) =>
            (Element t -> Bool -> t1 (a c)) -> Intersections t -> Bool -> t1 (a c)
applyIntersections fn (NoIntersection e) b    = intersectionElements fn e b
applyIntersections fn (IntersectionMark i e) b
    = intersectionConstraints (intersectionElements fn e b) (applyIntersections fn i False)


\end{code}

{\em intersectionConstraints} evaluates the intersection of constraints.
Note that {\em intersectionConstraints} needs to satisfy the rules regarding visibility
-- a non-PER visible constraint is simply ignored (X.691: B.2.2.10) --
and set operators and effective constraints (X.680: G.4.3.8). Non-PER visible constraints are ignored
in the definitions of {\tt foobar} and {\tt foobar1} by simply returning the other constraint. That is, if
the evaluation of a constraint results in a error being thrown -- which could only be a non-PER visible error --
then this is caught, thrown away and the other constraint returned.

\begin{code}

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

\end{code}

{\em intersectionElements} evaluates a constraint from an {\tt IntersectionElements} value.
There are two possible cases: a simple element constraint indicated by the constructor
{\em ElementConstraint} or an exclusion constraint (the set difference of two constraints)
indicated by the constructor {\em ExclusionConstraint). Note that for the {\em
ElementConstraint} case, the element-processing function which was provided as an input to the
top-level function {\em evaluateConstraint} is now applied to the element constraint. In the
other case the element-processing function is applied to each element constraint and {\em
exceptConstraints} is applied to their results.

\begin{code}

intersectionElements :: (ExtConstraint a,
             MonadError [Char] m,
             Lattice c,
             Constraint c) =>
            (Element t -> Bool -> m (a c)) -> IntersectionElements t -> Bool -> m (a c)
intersectionElements fn (ElementConstraint e) b  = fn e b
intersectionElements fn (ExclusionConstraint e (EXCEPT ex)) b
                = exceptConstraints (fn e b) (fn ex False)

\end{code}

{\em exceptConstraints} returns the set difference of constraints.
Note that {\em exceptConstraints} needs to satisfy the rules regarding visibility
-- a non-PER visible constraint is ignored if it is the exception value but makes the whole
constraint non-PER visible otherwise (X.691: B.2.2.10) --
and set operators and effective constraints (X.680: G.4.3.8).

\begin{code}

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

\end{code}

The the following section we present the element constraint-processing functions for ASN.1 types.

\subsection{Element Constraint-Processing Functions}
\label{contype}

For those types with PER-visible
constraints we present two functions:
\begin{itemize}
\item
one which processes the PER-visible constraints and returns an error message for the others. This function is prefixed in each case by {\em pv} and
is used in the evaluation of effective constraints.
\item
one which processes all applicable constraints. This function is used in the evaluation of validity-testing constraints.
\end{itemize}

All other types simply have a function used in the evaluation of validity-testing constraints.


\subsubsection{BooleanType}

{\em booleanElements} processes the various {\tt BooleanType} constraints, none of which are PER-visible.
Since all constraints are represented as potentially extensible constraints
with the boolean parameter indicating extensible constraint or not, the processing results in
a value of type {\em Either String (ExtensibleConstraint BoolConstraint)}. If a valid constraint
is evaluated then an {\em ExtensibleConstraint BoolConstraint} value is returned.

\begin{code}

booleanElements :: Element Bool -> Bool -> Either String (ExtensibleConstraint BooleanConstraint)
booleanElements (S (SV i)) b
    = return (makeExtensibleConstraint
                (BooleanConstraint [i]) top b)
booleanElements (C (Inc t)) b
    = containedBooleanType t []

\end{code}

{\em containedBooleanType} processes a contained {\tt BooleanType} constraint (X.680: 47.3).
Note that only the extension root values of an extensible contained type are used (X.680:
47.3.3). Thus the function {\em extensionRootOnly} is applied to the constraint returned by
{\em evaluateConstraint}.

\begin{code}

containedBooleanType :: ASNType Bool -> [SubtypeConstraint Bool]
               -> Either String (ExtensibleConstraint BooleanConstraint)
containedBooleanType (BuiltinType BOOLEAN) cl
    =  let  tp = ExtensibleConstraint top top False
            tpp = Right tp
        in
                extensionRootOnly $ evaluateConstraint booleanElements tpp cl
containedBooleanType (ConstrainedType t c) cl
    = containedBooleanType t (c:cl)

\end{code}

\subsubsection{IntegerType}

{\em pvIntegerElements} processes the various {\tt IntegerType} constraints which are all
PER-visible. Since all constraints are represented as potentially extensible constraints
with the boolean parameter indicating extensible constraint or not, the processing results in
a value of type {\em Either String (ExtensibleConstraint a)}. If a valid constraint
is evaluated then an {\em ExtensibleConstraint a} value is returned.

Since all {\tt IntegerType} constraints are PER-visible, this function may also be used
when evaluating a validity-testing constraint.

\begin{code}

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

\end{code}

{\em containedIntegerType} processes a contained {\tt IntegerType} constraint (X.680: 47.3).
Note that only the extension root values of an extensible contained type are used (X.680:
47.3.3). Thus the function {\em extensionRootOnly} is applied to the constraint returned by
{\em evaluateConstraint}.

\begin{code}

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

\end{code}

\subsubsection{EnumeratedType}

{\em enumeratedElements} processes the various {\tt EnumeratedType} constraints, none of which are PER-visible.
Since all constraints are represented as potentially extensible constraints
with the boolean parameter indicating extensible constraint or not, the processing results in
a value of type {\em Either String (ExtensibleConstraint EnumeratedConstraint)}. If a valid constraint
is evaluated then an {\em ExtensibleConstraint EnumeratedConstraint} value is returned.

\begin{code}

enumeratedElements :: Enumerate -> Element Enumerate -> Bool -> Either String (ExtensibleConstraint EnumeratedConstraint)
enumeratedElements en (S (SV (AddEnumeration ei EmptyEnumeration))) b
    = let (b, p) = validEnum en ei 0				 
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

		
validEnum :: Enumerate -> EnumerationItem -> Int -> (Bool, Maybe Int)
validEnum EmptyEnumeration ei n = (False, Nothing)
validEnum (AddEnumeration e r) ei n
					| e == ei = (True, Just n)
					| otherwise = validEnum r ei (n+1) 
validEnum (EnumerationExtensionMarker e) ei n
					= validEnum e ei n
						
\end{code}

{\em containedEnumeratedType} processes a contained {\tt EnumeratedType} constraint (X.680: 47.3).
Note that only the extension root values of an extensible contained type are used (X.680:
47.3.3). Thus the function {\em extensionRootOnly} is applied to the constraint returned by
{\em evaluateConstraint}.

\begin{code}

containedEnumeratedType :: Enumerate -> ASNType Enumerate -> [SubtypeConstraint Enumerate]
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

\end{code}
\subsubsection{BitStringType}

{- FIXME: Note that boolean is thrown away -}

{\em pvBitStringElements} processes the various {\tt BitStringType} constraints. The only PER-visible constraint
is the size constraint.

\begin{code}

pvBitStringElements :: (Constraint i,
            Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element BitString -> Bool -> Either String (ExtensibleConstraint i)
pvBitStringElements (SZ (SC v)) b  = evaluateSingleConstraint b pvIntegerElements v
pvBitStringElements (C (Inc c)) b  = throwError "Invisible!"
pvBitStringElements (S (SV v))  b  = throwError "Invisible!"

\end{code}

\subsubsection{OctetStringType}

{- FIXME: Note that boolean input is thrown away -}

{\em pvOctetStringElements} processes the various {\tt OctetStringType} constraints. The only PER-visible constraint
is the size constraint.

\begin{code}

pvOctetStringElements :: (Constraint i,
            Eq i,
            Show i,
            Lattice i,
            IntegerCon i) =>
            Element OctetString -> Bool -> Either String (ExtensibleConstraint i)
pvOctetStringElements (SZ (SC v)) b  = evaluateSingleConstraint b pvIntegerElements v
pvOctetStringElements (C (Inc c)) b  = throwError "Invisible!"
pvOctetStringElements (S (SV v))  b  = throwError "Invisible!"

\end{code}


{- FIXME: Note that boolean input is thrown away -}

{\em pvKnownMultiplierElements } processes the various known-multiplier restricted character string element constraints.
The only PER-visible element constraints are the size constraint, non-extensible permitted
alphabet constraint and type inclusion. For a non-extensible permitted alphabet constraint,
{\em evaluateSingleConstraint} is called with {\tt pvPermittedAlphabetElements} as a processing
function. The permitted alphabet element constraints are the same as the known-multiplier ones
but with the addition of the {\tt ValueRange} constraint.

{\em integerToKMConstraint} converts an {\tt IntegerType} constraint to a known-multiplier
constraint.

\begin{code}
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

\end{code}

{\em containedKnownMultType} processes a contained known-multiplier type constraint (X.680: 47.3).
Note that only the extension root values of an extensible contained type are used (X.680:
47.3.3). Thus the function {\em extensionRootOnly} is applied to the constraint returned by
{\em evaluateConstraint}.

\begin{code}

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

\end{code}






{- FIXME: Note that boolean value is thrown away -}

{\em pvSequenceOfElements} processes the various {\tt SequenceOfType} constraints. The only PER-visible constraint
is the size constraint.

\begin{code}

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


\end{code}
