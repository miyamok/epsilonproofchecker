module Test.VariableBinding where

-- test script for variable binding
--import Main
import Syntax
import Parser
import PrettyPrint
f1 = pf "all x ex y R(h(x, y), g(z))"

t1 = pt "f(x)"

f2 = termSubstitutionInFormula (Var "z" (-1) 0) t1 f1

f1str = prettyPrintFormula f2


compr1 = Compr [Var "z" (-1) 0] f1

t2 = pt "h1(y, x)"
f3 = comprehensionAndTermsToFormula compr1 [t2]

f4 = formulaSubstitutionInFormula (Pvar "P" (-1) 1) (Compr [Var "x" (-1) 0] (pf "Q(x)")) (pf "P(eps x P(x))")

main :: IO ()
main = do putStrLn $ prettyPrintFormula f1
          putStrLn $ prettyPrintFormula f2
          putStrLn $ prettyPrintFormula f3
