module Axiom where

import Syntax
import Data.List (nubBy, nub)
import Data.Maybe (catMaybes)
import Debug.Trace

isCriticalFormula :: Formula -> Bool
isCriticalFormula (ImpForm premise conclusion) = any (alphaEqFormula conclusion) reconcl
    where
        epsKernels = traceShowId $ catMaybes $ map epsTermToKernel (formulaToSubterms conclusion)
        substs = map (\kernel -> simpleFormulaUnificationAux premise kernel) epsKernels
        infos = filter (uncurry (\subst -> \epsKernel -> length subst == 1)) (zip substs epsKernels)
        reconcl = map (\pair -> let ([(VarTerm v, t)], f) = pair in epsTranslation $ ExistsForm v f) infos
isCriticalFormula _ = False

--isCriticalFormulaAux :: Formula -> Bool
isCriticalFormulaAux :: Formula -> [[(Term, Term)]]
isCriticalFormulaAux (ImpForm premise conclusion) = substs
    where
        epsKernels = catMaybes $ map epsTermToKernel (formulaToSubterms conclusion)
        substs = map (\kernel -> simpleFormulaUnification premise kernel) epsKernels
        infos = filter (uncurry (\subst -> \epsKernel -> length subst == 1)) (zip substs epsKernels)
        reconcl = map (\pair -> let ([(VarTerm v, t)], f) = pair in epsTranslation $ ExistsForm v f) infos
        result = any (\f -> alphaEqFormula f conclusion) reconcl

simpleFormulaUnification :: Formula -> Formula -> [(Term, Term)]
simpleFormulaUnification f g = nubBy alphaEqTermPair (simpleFormulaUnificationAux f g)

simpleFormulaUnificationAux :: Formula -> Formula -> [(Term, Term)]
simpleFormulaUnificationAux (PredForm p ts) (PredForm p' ts') =
    if (p == p') && (length ts == length ts') then concat $ map (uncurry simpleTermUnificationAux) (zip ts ts') else []
simpleFormulaUnificationAux (ImpForm f g) (ImpForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (ConjForm f g) (ConjForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (DisjForm f g) (DisjForm f' g') = simpleFormulaUnificationAux f f' ++ simpleFormulaUnificationAux g g'
simpleFormulaUnificationAux (NegForm f) (NegForm f') = simpleFormulaUnificationAux f f'
simpleFormulaUnificationAux (ForallForm v f) (ForallForm v' f') = simpleFormulaUnificationAux g g'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = substFormula v freshvarterm f
        g' = substFormula v' freshvarterm f'
simpleFormulaUnificationAux (ExistsForm v f) (ExistsForm v' f') = simpleFormulaUnificationAux f f'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = substFormula v freshvarterm f
        g' = substFormula v' freshvarterm f'
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
        g = substFormula v freshvarterm f
        g' = substFormula v' freshvarterm f'

alphaEqTermPair :: (Term, Term) -> (Term, Term) -> Bool
alphaEqTermPair (t1, t2) (s1, s2) = alphaEqTerm t1 s1 && alphaEqTerm t2 s2
