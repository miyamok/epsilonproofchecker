module PrettyPrint where
import Syntax
import Data.List

prettyPrintPredicate :: Predicate -> String
prettyPrintPredicate (Pred n i a)
 | i /= -1 = n ++ show i
 | otherwise = n

prettyPrintFormula :: Formula -> String
-- prettyPrintFormula f p =
--     let ppFla = case f of
--          (PredForm p ts) | null ts -> if predToArity p == 0 then ppPred else ppPred ++ "()"
--                          | otherwise -> ppPred
--                          where ppPred = prettyPrintPredicate p
--          (NegForm f) -> "~" 
--  in if p then "(" ++ ppFla ++ ")" else ppFla

-- prettyPrintFormula (PredForm p ts) parens
-- let ppFla 
--      | null ts = if predToArity p == 0 then ppPred else ppPred ++ "()"
--      | otherwise = ppPred
--      where ppPred = prettyPrintPredicate p

-- in if parens then "(" ++ ppFla ++ ")" else ppFla
prettyPrintFormula (PredForm p ts)
 | null ts = if predToArity p == 0 then ppPred else ppPred ++ "()"
 | otherwise = ppPred ++ ppArgs
 where ppPred = prettyPrintPredicate p
       ppArgs = prettyPrintArgTerms ts
prettyPrintFormula (NegForm f) = "~" ++ if isBiconForm f then "(" ++ ppFla ++ ")" else ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ExistsForm v f) = "ex " ++ prettyPrintVariable v ++ " " ++ if isBiconForm f then "(" ++ ppFla ++ ")" else ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ForallForm v f) = "all " ++ prettyPrintVariable v ++ " " ++ if isBiconForm f then "(" ++ ppFla ++ ")" else ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ImpForm f f') = ppFla ++ " -> " ++ ppFla'
 where ppFlaAux = prettyPrintFormula f
       ppFla = if isImpForm f then "(" ++ ppFlaAux ++ ")" else ppFlaAux
       ppFla' = prettyPrintFormula f'
prettyPrintFormula (DisjForm f f') = ppFla ++ " | " ++ ppFla'
 where ppFla = prettyPrintFormula f
       ppFlaAux = prettyPrintFormula f'
       ppFla' = if isImpForm f' || isDisjForm f' then "(" ++ ppFlaAux ++ ")" else ppFlaAux
prettyPrintFormula (ConjForm f f') = ppFla ++ " & " ++ ppFla'
 where ppFla = prettyPrintFormula f
       ppFlaAux = prettyPrintFormula f'
       ppFla' = if isBiconForm f' then "(" ++ ppFlaAux ++ ")" else ppFlaAux

prettyPrintVariable :: Variable -> String
prettyPrintVariable (Var n i)
 | i /= -1 = n ++ show i
 | otherwise = n

prettyPrintConstant :: Constant -> String
prettyPrintConstant (Const n i a)
 | i /= -1 = n ++ show i
 | otherwise = n

prettyPrintArgTerms :: [Term] -> String
prettyPrintArgTerms ts
 | null ts = ""
 | otherwise = "(" ++ intercalate ", " (map prettyPrintTerm ts) ++ ")"

prettyPrintTerm :: Term -> String
prettyPrintTerm (VarTerm v) = prettyPrintVariable v
prettyPrintTerm (AppTerm c ts)
 | null ts = prettyPrintConstant c
 | otherwise = prettyPrintConstant c ++ prettyPrintArgTerms ts
prettyPrintTerm (EpsTerm v f) = concat ["eps ", prettyPrintVariable v, ppKer]
    where
        ppFla = prettyPrintFormula f
        ppKer = if isBiconForm f then "(" ++ ppFla ++ ")" else " " ++ ppFla
