module Axiom where
import Syntax
import Data.List (nubBy, nub, findIndex, splitAt, delete)
import Data.Maybe (catMaybes)
import Data.Either

type VarOrPvar = Either Variable Predicate
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

isRigidTerm :: [VarOrPvar] -> Term -> Bool
isRigidTerm rigidVars (VarTerm v) = Left v `elem` rigidVars
isRigidTerm _ _ = True

isRigidFormula :: [Predicate] -> Formula -> Bool
isRigidFormula rigidPvars (PredForm Falsum _) = True
isRigidFormula rigidPvars (PredForm Equality _) = True
isRigidFormula rigidPvars (PredForm p _) = p `elem` rigidPvars
isRigidFormula _ _ = True

unifyTerms :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Term, Term)] -> [Binding]
unifyTerms = unifyTermsAux unificationBound

unifyTermsAux :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Term, Term)] -> [Binding]
unifyTermsAux 0 _ _ _ _ = []
unifyTermsAux bound sigs flexs forbs [] = []
unifyTermsAux bound sigs flexs forbs ((t,t'):pairs)
 | alphaEqTerm t t' = unifyTermsAux (bound-1) sigs flexs forbs pairs
 | isRigidTerm rigids t && isRigidTerm rigids t' =
    case (t, t') of (EpsTerm v f, EpsTerm v' f') -> undefined
                    (AppTerm c ts, AppTerm c' ts') ->
                        if c == c' then unifyTermsAux (bound-1) sigs flexs forbs (zip ts ts' ++ pairs)
                                   else []
                    otherewise -> []
 | isRigidTerm rigids t && not (isRigidTerm rigids t') = unifyTermsAux (bound-1) sigs flexs forbs ((t',t):pairs)
 | not (isRigidTerm rigids t) && isRigidTerm rigids t' =
    case t of VarTerm v -> let newPair = (termSubstitutionInTerm v t' t, termSubstitutionInTerm v t' t')
                                in unifyTermsAux (bound-1) sigs flexs forbs (newPair:pairs)
 | not (isRigidTerm rigids t) && not (isRigidTerm rigids t') =
    let x = do i <- findIndex (\(s, s') -> isRigidTerm rigids s || isRigidTerm rigids s') pairs
               let (h, t) = splitAt i pairs
               return (head t:h ++ tail t) 
      in case x of Just pairs' -> unifyTermsAux (bound-1) sigs flexs forbs (pairs' ++ [(t, t')])
                   Nothing -> let freshVar = variablesToFreshVariable $ lefts(sigs ++ flexs ++ forbs)
                                  freshVarTerm = VarTerm freshVar
                                  (ts0, ts1) = unzip ((t,t'):pairs)
                                in map (\s -> Left(varTermToVar s, freshVarTerm)) (ts0 ++ ts1)
 where
    rigids = sigs++forbs

-- unifyTerms (VarTerm v) t = [ Left (v, t) | VarTerm v == t ]
-- unifyTerms t (VarTerm v) = [ Left (v, t) | VarTerm v == t ]
-- unifyTerms (AppTerm c ts) (AppTerm c' ts') = if c /= c' then [] else concat $ zipWith unifyTerms ts ts'
-- unifyTerms (EpsTerm v f) (EpsTerm v' f') =  undefined

unifyFormulas :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Formula, Formula)] -> [Binding]
unifyFormulas = unifyFormulasAux unificationBound

unifyFormulasAux :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Formula, Formula)] -> [Binding]
unifyFormulasAux 0 _ _ _ _ = []
unifyFormulasAux _ _ _ _ [] = []
unifyFormulasAux bound sigs flexs forbs ((f, g):pairs)
 | alphaEqFormula f g = unifyFormulasAux (bound-1) sigs flexs forbs pairs
 | isRigidFormula rigidPreds f && isRigidFormula rigidPreds g =
    case (f, g) of (ImpForm f1 f2, ImpForm g1 g2) -> unifyFormulasAux (bound-1) sigs flexs forbs ((f1,g1):(f2,g2):pairs)
                   (ConjForm f1 f2, ConjForm g1 g2) -> unifyFormulasAux (bound-1) sigs flexs forbs ((f1,g1):(f2,g2):pairs)
                   (DisjForm f1 f2, ConjForm g1 g2) -> unifyFormulasAux (bound-1) sigs flexs forbs ((f1,g1):(f2,g2):pairs)
                   (ForallForm v f', ForallForm u g') ->
                    let freshVar = variablesToFreshVariable $ lefts(sigs ++ flexs ++ forbs)
                        freshVarTerm = VarTerm freshVar
                        f1 = termSubstitutionInFormula v freshVarTerm f'
                        g1 = termSubstitutionInFormula u freshVarTerm g'
                     in unifyFormulasAux (bound-1) sigs flexs (Left freshVar:forbs) ((f1,g1):pairs)
                   (ExistsForm v f', ExistsForm u g') ->
                    let freshVar = variablesToFreshVariable $ lefts(sigs ++ flexs ++ forbs)
                        freshVarTerm = VarTerm freshVar
                        f1 = termSubstitutionInFormula v freshVarTerm f'
                        g1 = termSubstitutionInFormula u freshVarTerm g'
                     in unifyFormulasAux (bound-1) sigs flexs (Left freshVar:forbs) ((f1,g1):pairs)
                   --fla -> fla $ undefined
 | not (isRigidFormula rigidPreds f) && isRigidFormula rigidPreds g =
    -- NOTE: projection case never happens. only imitation case
    let (bindings, flexs') = unifyFormulasAuxFlexRigid sigs flexs forbs f g
        flexPvar = predicateFormToPredicate f
        newFlexs = delete (Right flexPvar) flexs++flexs'
     in unifyFormulasAux (bound-1) sigs newFlexs forbs ((f, g):pairs)
 | isRigidFormula rigidPreds f && not (isRigidFormula rigidPreds g) = unifyFormulasAux (bound-1) sigs flexs forbs ((g, f):pairs)
 | not (isRigidFormula rigidPreds f) && not (isRigidFormula rigidPreds g) =
    let x = do i <- findIndex (\(f', g') -> isRigidFormula rigidPreds f' || isRigidFormula rigidPreds g') pairs
               let (h, t) = splitAt i pairs
               return (head t:h ++ tail t)
      in case x of Just pairs' -> unifyFormulasAux (bound-1) sigs flexs forbs (pairs' ++ [(f, g)])
                   Nothing -> let knownPreds = concat $ map formulaToPredicates (let (x, y) = unzip ((f, g):pairs) in x++y)
                                in concat $ map (uncurry $ unifyFormulasAuxFlexFlex knownPreds) ((f, g):pairs)
 where
    rigidPreds = [] -- additional arguments, sigPreds, flexPreds, and forbPreds, are required.

-- taking care of the imitation case.  the projection case doesn't happen and is safely ignored.
unifyFormulasAuxFlexRigid :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> Formula -> Formula -> ([Binding], [VarOrPvar])
unifyFormulasAuxFlexRigid sigs flexs forbs (PredForm p ts) g =
    let pArity = length ts
        rigids = sigs ++ forbs
        newVars = variablesToFreshVariables pArity []
        newVarTerms = map VarTerm newVars
        gArity = case g of PredForm Falsum _ -> 0
                           ForallForm _ _ -> 1
                           ExistsForm _ _ -> 1
                           _ -> 2
        --newPvars = predicateVariablesAndArityToFreshPredicateVariables (p:rigidPreds ++ flexPvars) gArity
        newPvars = predicateVariablesAndArityToFreshPredicateVariables pArity (p:rights (rigids ++ flexs)) gArity
        newArgFlas = map (\newPvar -> PredForm newPvar newVarTerms) newPvars
        comprFla = case g of PredForm Falsum _ -> PredForm Falsum []
                             -- PredForm (Equality []) -> 
                             -- here, object arguments appear for Equality
                             ForallForm v _ -> ForallForm v (head newArgFlas)
                             ExistsForm v _ -> ExistsForm v (head newArgFlas)
                             ImpForm _ _ -> ImpForm (head newArgFlas) (last newArgFlas)
                             ConjForm _ _ -> ConjForm (head newArgFlas) (last newArgFlas)
                             DisjForm _ _ -> DisjForm (head newArgFlas) (last newArgFlas)
        binding = Right(p, Compr newVars comprFla)
     in ([binding], map Right newPvars)

unifyFormulasAuxFlexFlex :: [Predicate] -> Formula -> Formula -> [Binding]
unifyFormulasAuxFlexFlex knownPreds f g =
    let freshPredicate = predicateVariablesAndArityToFreshPredicateVariable knownPreds 0
        p1 = predicateFormToPredicate f
        p2 = predicateFormToPredicate g
        a1 = predicateToArity p1
        a2 = predicateToArity p2
        vs1 = variablesToFreshVariables a1 []
        vs2 = variablesToFreshVariables a2 []
        cmp1 = Compr vs1 (PredForm freshPredicate [])
        cmp2 = Compr vs2 (PredForm freshPredicate [])
     in [Right(p1,cmp1), Right(p2,cmp2)]