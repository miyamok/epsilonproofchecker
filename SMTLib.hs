module SMTLib where
import Syntax
import PrettyPrint (prettyPrintVariable, prettyPrintPredicate, prettyPrintConstant, prettyPrintTerm)
import Data.List
import System.Process
import Debug.Trace

par :: [String] -> String
par ss = "(" ++ intercalate " " ss ++ ")"

predToSMTLibExpr :: Predicate -> String
predToSMTLibExpr Falsum = "false"
predToSMTLibExpr Equality = "="
predToSMTLibExpr (Pvar n i a) = prettyPrintPredicate (Pvar n i a)

formulaToSMTLibExpr :: Formula -> String
formulaToSMTLibExpr (PredForm p []) = predToSMTLibExpr p
formulaToSMTLibExpr (PredForm p ts) = par (predToSMTLibExpr p:map termToSMTLibExpr ts)
formulaToSMTLibExpr (ImpForm f f') = par ("=>":map formulaToSMTLibExpr [f, f'])
formulaToSMTLibExpr (ConjForm f f') = par ("and":map formulaToSMTLibExpr [f, f'])
formulaToSMTLibExpr (DisjForm f f') = par ("or":map formulaToSMTLibExpr [f, f'])
formulaToSMTLibExpr (ForallForm v f) = par ["forall", par [par [prettyPrintVariable v, "Type"]], formulaToSMTLibExpr f]
formulaToSMTLibExpr (ExistsForm v f) = par ["exists", par [par [prettyPrintVariable v, "Type"]], formulaToSMTLibExpr f]

termToSMTLibExpr :: Term -> String
termToSMTLibExpr (VarTerm v) = prettyPrintVariable v
termToSMTLibExpr (AppTerm c []) = prettyPrintConstant c
termToSMTLibExpr (AppTerm c ts) = par (prettyPrintConstant c:map termToSMTLibExpr ts)
termToSMTLibExpr (EpsTerm v f) = undefined

formulaToSMTLibDeclaration :: Formula -> String
formulaToSMTLibDeclaration f = concat [varDeclarations, constDeclarations, predicateDeclarations]
    where
        varDeclarations = concat $ map variableToSMTLibDeclaration (formulaToFreeVariables f)
        constDeclarations = concat $ map constantToSMTLibDeclaration (formulaToConstants f)
        predicateDeclarations = concat $ map predicateVariableToSMTLibDeclaration (formulaToPredicateVariables f)

sMTLibPreamble :: String
sMTLibPreamble = "(declare-sort Type)"

assertSMTLib :: Formula -> String
assertSMTLib f = sMTLibPreamble ++ formulaToSMTLibDeclaration f ++ "(assert (not " ++ formulaToSMTLibExpr f ++ "))" ++ "(check-sat)"

checkByZ3 :: String -> IO Bool
checkByZ3 smtstr = do out <- readProcess "z3" ["-in"] smtstr
                      return ("unsat\n" == out)

variableToSMTLibDeclaration :: Variable -> String
variableToSMTLibDeclaration v = par ["declare-const", prettyPrintVariable v, "Type"]

constantToSMTLibDeclaration :: Constant -> String
constantToSMTLibDeclaration (Const n i a) =
    par ["declare-fun", prettyPrintConstant (Const n i a), par $ replicate a "Type", "Type"]

predicateVariableToSMTLibDeclaration :: Predicate -> String
predicateVariableToSMTLibDeclaration (Pvar n i a) =
    par ["declare-fun", prettyPrintPredicate (Pvar n i a), par $ replicate a "Type", "Bool"]

checkFormulaByZ3 :: Formula -> IO Bool
checkFormulaByZ3 f = checkByZ3 (assertSMTLib f)
