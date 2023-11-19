module Test.Unification where
import Axiom
import Syntax
import PrettyPrint
import Parser(pt, pf)
import Main
import Proof

-- x=f(c)
t = unify [] [Left(Var "x" (-1) 0)] [] [Left ((pt "x"),(pt "f (c)"))]

-- x=y
t1 = unify [Left (Var "y" (-1)  0)] [Left(Var "x" (-1) 0)] [] [Left ((pt "x"),(pt "y"))]

-- A=B
f = unify [Right(Pvar "B" (-1) 0)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "B")]

-- P(x)=P(c)
f0 = unify [Right(Pvar "P" (-1) 1)] [Left (Var "x" (-1) 0)] [] [Right (pf "P(x)", pf "P(c)")]

-- A=P(c)
f1 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "P(c)")]

-- A=P(x)
f2err = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "P(x)")]
--A=P(x)
f2 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0), Left(Var "x" (-1) 0)] [] [Right (pf "A", pf "P(x)")]
-- A=P(x)
f3' = unify [Right(Pvar "P" (-1) 1), Left (Var "x" (-1) 0)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "P(x)")]

-- not yet working for quantified formulas
-- A = all x P(x)
f3 = unify [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] [Right (pf "A", pf "all x P(x)")]

f4 = unify [Right(Pvar "P" (-1) 1), Left (Var "x" (-1) 0)] [Right(Pvar "A" (-1) 0), Right(Pvar "B" (-1) 0)] [] [Right (pf "A", pf "all x P(x)")]

test = do
    putStrLn $ show $ isUnifiablePair [Left (Var "y" (-1) 0)] [Left(Var "x" (-1) 0)] [] (Left ((pt "x"),(pt "y")))
    putStrLn $ show $ isUnifiablePair [] [Left(Var "x" (-1) 0)] [] (Left ((pt "x"),(pt "f (c)")))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "B" (-1) 0)] [Right(Pvar "A" (-1) 0)] [] (Right (pf "A", pf "B"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0),Left(Var "x" (-1) 0)] [] (Right (pf "A", pf "P(x)"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Left (Var "x" (-1) 0)] [] (Right (pf "P(x)", pf "P(c)"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] (Right (pf "A", pf "P(c)"))
    --putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] (Right (pf "A", pf "P(x)"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0), Left(Var "x" (-1) 0)] [] (Right (pf "A", pf "P(x)"))
    
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] (Right (pf "A", pf "all x P(x)"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1)] [Right(Pvar "A" (-1) 0)] [] (Right (pf "A", pf "all x P(x)"))
    -- putStrLn $ prettyPrintFormula f3l
    -- putStrLn $ prettyPrintFormula f3r
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1), Right(Pvar "C" (-1) 0)] [Right(Pvar "A" (-1) 0), Right(Pvar "B" (-1) 0)] [] (Right (pf "A -> B", pf "P(c) -> C"))
    putStrLn $ show $ isUnifiablePair [Right(Pvar "P" (-1) 1), Right(Pvar "C" (-1) 0)] [Right(Pvar "A" (-1) 0), Right(Pvar "B" (-1) 0)] [] (Right (pf "A -> B", pf "(C -> C) -> C"))
