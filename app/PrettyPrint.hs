module PrettyPrint where
import Syntax
import Proof
import Data.List
import Unification

prettyPrintPredicate :: Predicate -> String
prettyPrintPredicate (Pvar n i a)
 | i /= -1 = n ++ show i
 | otherwise = n
prettyPrintPredicate Falsum = "bot"

prettyPrintFormula :: Formula -> String
prettyPrintFormula (PredForm p ts)
 | null ts = if predicateToArity p == 0 then ppPred else ppPred ++ "()"
 | otherwise = ppPred ++ ppArgs
 where ppPred = prettyPrintPredicate p
       ppArgs = prettyPrintArgTerms ts
prettyPrintFormula (ExistsForm v f) = "ex " ++ prettyPrintVariable v ++ if isBiconForm f then "(" ++ ppFla ++ ")" else " " ++ ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ForallForm v f) = "all " ++ prettyPrintVariable v ++ if isBiconForm f then "(" ++ ppFla ++ ")" else " " ++ ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ImpForm f (PredForm Falsum [])) = "~" ++ if isBiconForm f then "(" ++ ppFla ++ ")" else ppFla
 where ppFla = prettyPrintFormula f
prettyPrintFormula (ImpForm f f') = ppFla ++ " -> " ++ ppFla'
 where ppFlaAux = prettyPrintFormula f
       ppFla = if isImpFormula f then "(" ++ ppFlaAux ++ ")" else ppFlaAux
       ppFla' = prettyPrintFormula f'
prettyPrintFormula (DisjForm f f') = ppFla ++ " | " ++ ppFla'
 where ppFlaAux = prettyPrintFormula f
       ppFla = if isImpFormula f then "(" ++ ppFlaAux ++ ")" else ppFlaAux
       ppFlaAux' = prettyPrintFormula f'
       ppFla' = if isImpFormula f' || isDisjForm f' then "(" ++ ppFlaAux' ++ ")" else ppFlaAux'
prettyPrintFormula (ConjForm f f') = ppFla ++ " & " ++ ppFla'
 where ppFla = prettyPrintFormula f
       ppFlaAux = prettyPrintFormula f'
       ppFla' = if isBiconForm f' then "(" ++ ppFlaAux ++ ")" else ppFlaAux

prettyPrintVariable :: Variable -> String
prettyPrintVariable (Var n i _)
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
prettyPrintTerm (AppTerm t1 t2)
 | null ts = prettyPrintTerm t
 | otherwise = prettyPrintTerm t ++ prettyPrintArgTerms ts
 where
    t:ts = appTermToTerms (AppTerm t1 t2)
prettyPrintTerm (ConstTerm c) = prettyPrintConstant c
prettyPrintTerm (EpsTerm v f) = concat ["eps ", prettyPrintVariable v, ppKer]
    where
        ppFla = prettyPrintFormula f
        ppKer = if isBiconForm f then "(" ++ ppFla ++ ")" else " " ++ ppFla

prettyPrintReason :: Rule -> String
prettyPrintReason r = case r of (MP Nothing Nothing) -> "MP"
                                (MP (Just s) (Just s')) -> "MP(" ++ s ++ ", " ++ s' ++ ")"
                                (Gen Nothing) -> "Gen"
                                (Gen (Just s)) -> "Gen(" ++ s ++ ")"
                                (Use s) -> "Use(" ++ s ++ ")"
                                r -> show r

prettyPrintProofStep :: Step -> String
prettyPrintProofStep (f, r, t) = intercalate " " ([prettyPrintFormula f, "by", prettyPrintReason r] ++ l)
    where
        l = case t of Nothing -> []
                      Just s -> [prettyPrintTag t]

prettyPrintTag :: Tag -> String
prettyPrintTag Nothing = ""
prettyPrintTag (Just s) = "#" ++ s

prettyPrintProof :: Proof -> String
prettyPrintProof p = intercalate "\n" (map prettyPrintProofStep p)

prettyPrintJudgment :: [Formula] -> Formula -> String
prettyPrintJudgment [] concl = "⊢ " ++ prettyPrintFormula concl
prettyPrintJudgment asms concl = prettyPrintAssumptions asms ++ " ⊢ " ++ prettyPrintFormula concl

prettyPrintAssumptions :: [Formula] -> String
prettyPrintAssumptions fs = intercalate ", " (map prettyPrintFormula fs)

prettyPrintUnificationPair :: UnificationPair -> String
prettyPrintUnificationPair (Left (x,y)) = prettyPrintTerm x ++ " ?=? " ++ prettyPrintTerm y
prettyPrintUnificationPair (Right (x,y)) = prettyPrintFormula x ++ " ?=? " ++ prettyPrintFormula y