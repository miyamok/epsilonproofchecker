module Test.Unification where
import Axiom (unify)
import Syntax
import PrettyPrint
import Parser(pt, pf)
import Main
import Proof

t = unify [] [Left(Var "x" (-1))] [] [Left ((pt "x"),(pt "f (c)"))]

f = unify [Right(Pvar "B" (-1) 0)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "B")]

f0 = unify [Right(Pvar "P" (-1) 1)] [Left (Var "x" (-1))] [] [Right (pf "P(x)", pf "P(c)")]

f1 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "P(c)")]

f2err = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "P(x)")]
f2 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0), Left(Var "x" (-1))] [] [Right (pf "A", pf "P(x)")]

-- not yet working for quantified formulas
f3 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "all x P(x)")]
