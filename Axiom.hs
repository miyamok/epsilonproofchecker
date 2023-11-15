module Axiom where
import Syntax
import Data.List (nubBy, nub, findIndex, splitAt)
import Data.Maybe (catMaybes)
import Debug.Trace

unificationBound :: Int
unificationBound = 1000

isCriticalFormula :: Formula -> Bool
isCriticalFormula (ImpForm premise conclusion) = any (alphaEqFormula conclusion) concl'
    where
        epsKernels = catMaybes $ map epsTermToKernel (formulaToSubterms conclusion)
        substs = map (\kernel -> simpleFormulaUnification premise kernel) epsKernels
        infos = filter (\(subst, epsKernel) -> length subst == 1) (zip substs epsKernels)
        concl' = map (\pair -> let ([(VarTerm v, t)], f) = pair in epsTranslation $ ExistsForm v f) infos
isCriticalFormula _ = False

simpleFormulaUnification :: Formula -> Formula -> [(Term, Term)]
simpleFormulaUnification f g = nubBy alphaEqTermPair (simpleFormulaUnificationAux f g)

simpleFormulaUnificationAux :: Formula -> Formula -> [(Term, Term)]
simpleFormulaUnificationAux (PredForm p ts) (PredForm p' ts') =
    if (p == p') && (length ts == length ts') then concat $ map (uncurry simpleTermUnificationAux) (zip ts ts') else []
simpleFormulaUnificationAux (ImpForm f g) (ImpForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (ConjForm f g) (ConjForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (DisjForm f g) (DisjForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (ForallForm v f) (ForallForm v' f') = simpleFormulaUnificationAux g g'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = termSubstitutionInFormula v freshvarterm f
        g' = termSubstitutionInFormula v' freshvarterm f'
simpleFormulaUnificationAux (ExistsForm v f) (ExistsForm v' f') = simpleFormulaUnificationAux f f'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = termSubstitutionInFormula v freshvarterm f
        g' = termSubstitutionInFormula v' freshvarterm f'
simpleFormulaUnificationAux f f' = []

simpleTermUnification :: Term -> Term -> [(Term, Term)]
simpleTermUnification t s = nubBy alphaEqTermPair (simpleTermUnificationAux t s)

simpleTermUnificationAux :: Term -> Term -> [(Term, Term)]
simpleTermUnificationAux (VarTerm v) (VarTerm v')
  | v == v' = []
  | v <= v' = [(VarTerm v, VarTerm v')]
  | otherwise = [(VarTerm v', VarTerm v)]
simpleTermUnificationAux (VarTerm v) t = [(VarTerm v, t)]
simpleTermUnificationAux t (VarTerm v) = [(VarTerm v, t)]
simpleTermUnificationAux (AppTerm c ts) (AppTerm c' ts') = concat $ map (uncurry simpleTermUnificationAux) (zip ts ts')
simpleTermUnificationAux (EpsTerm v f) (EpsTerm v' f') = simpleFormulaUnificationAux g g'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = termSubstitutionInFormula v freshvarterm f
        g' = termSubstitutionInFormula v' freshvarterm f'

alphaEqTermPair :: (Term, Term) -> (Term, Term) -> Bool
alphaEqTermPair (t1, t2) (s1, s2) = alphaEqTerm t1 s1 && alphaEqTerm t2 s2

isRigidTerm :: Term -> Bool
isRigidTerm (VarTerm _) = False
isRigidTerm _ = True

isRigidFormula :: Formula -> Bool
isRigidFormula (PredForm (Pred _ _ _) _) = False
isRigidFormula _ = True

unifyTerms :: [Variable] -> [Variable] -> [Variable] -> [(Term, Term)] -> [Binding]
unifyTerms = unifyTermsAux unificationBound

unifyTermsAux :: Int -> [Variable] -> [Variable] -> [Variable] -> [(Term, Term)] -> [Binding]
unifyTermsAux 0 _ _ _ _ = []
unifyTermsAux bound sigVars flexVars forbVars [] = []
unifyTermsAux bound sigVars flexVars forbVars ((t,t'):pairs)
 | alphaEqTerm t t' = unifyTermsAux (bound-1) sigVars flexVars forbVars pairs
 | isRigidTerm t && isRigidTerm t' =
    case (t, t') of (EpsTerm v f, EpsTerm v' f') -> undefined
                    (AppTerm c ts, AppTerm c' ts') ->
                        if c == c' then unifyTermsAux (bound-1) sigVars flexVars forbVars (zip ts ts' ++ pairs)
                                   else []
                    otherewise -> []
 | isRigidTerm t && not (isRigidTerm t') = unifyTermsAux (bound-1) sigVars flexVars forbVars ((t',t):pairs)
 | not (isRigidTerm t) && isRigidTerm t' =
    case t of VarTerm v -> let newPair = (termSubstitutionInTerm v t' t, termSubstitutionInTerm v t' t')
                                in unifyTermsAux (bound-1) sigVars flexVars forbVars (newPair:pairs)
 | not (isRigidTerm t) && not (isRigidTerm t') =
    let x = do i <- findIndex (\(s, s') -> isRigidTerm s || isRigidTerm s') pairs
               let (h, t) = splitAt i pairs
               return (head t:h ++ tail t) 
      in case x of Just pairs' -> unifyTermsAux (bound-1) sigVars flexVars forbVars (pairs' ++ [(t, t')])
                   Nothing -> let freshVar = variablesToFreshVariable (sigVars ++ flexVars ++ forbVars)
                                  freshVarTerm = VarTerm freshVar
                                  (ts0, ts1) = unzip ((t,t'):pairs)
                                in map (\s -> Left(varTermToVar s, freshVarTerm)) (ts0 ++ ts1)

-- unifyTerms (VarTerm v) t = [ Left (v, t) | VarTerm v == t ]
-- unifyTerms t (VarTerm v) = [ Left (v, t) | VarTerm v == t ]
-- unifyTerms (AppTerm c ts) (AppTerm c' ts') = if c /= c' then [] else concat $ zipWith unifyTerms ts ts'
-- unifyTerms (EpsTerm v f) (EpsTerm v' f') =  undefined

-- unifyFormulas :: [Variable] -> [Variable] -> [Variable] -> [(Formula, Formula)] -> [Binding]
-- unifyFormulas (PredForm p ts) (PredForm p' ts') = 