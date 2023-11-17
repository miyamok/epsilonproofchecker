module Axiom where
import Syntax
import Data.List (nubBy, nub, findIndex, splitAt, delete)
import Data.Maybe (catMaybes)
import Data.Either

type VarOrPvar = Either Variable Predicate
type TermOrForm = Either Term Formula
type Binding = Either (Variable, Term) (Predicate, Comprehension)

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

isRigidFormula :: [VarOrPvar] -> Formula -> Bool
isRigidFormula rigidPvars (PredForm Falsum _) = True
isRigidFormula rigidPvars (PredForm Equality _) = True
isRigidFormula rigidPvars (PredForm p _) = Right p `elem` rigidPvars
isRigidFormula _ _ = True

isRigid :: [VarOrPvar] -> Either Term Formula -> Bool
isRigid rigids (Left t) = isRigidTerm rigids t
isRigid rigids (Right f) = isRigidFormula rigids f

unify :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [Either (Term, Term) (Formula, Formula)] -> [Binding]
unify = unifyAux unificationBound

unifyAux :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [Either (Term, Term) (Formula, Formula)] -> [Binding]
unifyAux _ _ _ _ [] = []
unifyAux 0 _ _ _ _ = []
unifyAux bound sigs flexs forbs (Left (t1, t2):pairs)
 | alphaEqTerm t1 t2 = unifyAux (bound-1) sigs flexs forbs pairs
 | isRigidTerm rigids t1 && isRigidTerm rigids t2 =
    case (t1, t2) of (EpsTerm v1 f1, EpsTerm v2 f2) -> undefined
                     (AppTerm c1 ts1, AppTerm c2 ts2) ->
                        if c1 == c2 then unifyAux (bound-1) sigs flexs forbs (map Left (zip ts1 ts2)++pairs)
                        else []
                     _ -> []
 | isRigidTerm rigids t1 && not (isRigidTerm rigids t2) = unifyAux (bound-1) sigs flexs forbs (Left (t2,t1):pairs)
 | not (isRigidTerm rigids t1) && isRigidTerm rigids t2 =
    let x = do i <- findIndex (\pair -> case pair of Left(s1, s2) -> isRigidTerm rigids s1 || isRigidTerm rigids s2
                                                     Right(f1, f2) -> isRigidFormula rigids f1 || isRigidFormula rigids f2) pairs
               let (h, t) = splitAt i pairs
               return (head t:h ++ tail t)
      in case x of Just pairs' -> unifyAux (bound-1) sigs flexs forbs (pairs' ++ [Left (t1, t2)])
                   Nothing -> unifyFlexFlex sigs flexs forbs (Left (t1, t2):pairs)
                    
                    --  let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
                    --               freshVarTerm = VarTerm freshVar
                    --               pairs' = filter isRight pairs
                    --               (ls,rs) = unzip $ map (\x -> case x of Left t -> t; _ -> undefined) (filter isLeft pairs)
                    --               ts' :: [Binding] = map (\s -> Left (varTermToVar s, freshVarTerm)) (ls++rs)
                    --             in ts' ++ unifyAux (bound -1) sigs flexs forbs pairs'
 where
    rigids = sigs ++ forbs
unifyAux bound sigs flexs forbs (Right (f1, f2):pairs)
 | alphaEqFormula f1 f2 = unifyAux (bound-1) sigs flexs forbs pairs
 | isRigidFormula rigids f1 && isRigidFormula rigids f2 =
    case (f1, f2) of (ImpForm f1' f2', ImpForm g1' g2') -> unifyAux (bound-1) sigs flexs forbs (Right (f1',g1'):Right (f2',g2'):pairs)
                     (ConjForm f1' f2', ConjForm g1' g2') -> unifyAux (bound-1) sigs flexs forbs (Right (f1',g1'):Right (f2',g2'):pairs)
                     (DisjForm f1' f2', DisjForm g1' g2') -> unifyAux (bound-1) sigs flexs forbs (Right (f1',g1'):Right (f2',g2'):pairs)
                     (ForallForm v f', ForallForm u g') ->
                      let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
                          freshVarTerm = VarTerm freshVar
                          f1' = termSubstitutionInFormula v freshVarTerm f'
                          g1' = termSubstitutionInFormula u freshVarTerm g'
                       in unifyAux (bound-1) sigs flexs (Left freshVar:forbs) (Right (f1',g1'):pairs)
                     (ExistsForm v f', ExistsForm u g') ->
                      let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
                          freshVarTerm = VarTerm freshVar
                          f1' = termSubstitutionInFormula v freshVarTerm f'
                          g1' = termSubstitutionInFormula u freshVarTerm g'
                       in unifyAux (bound-1) sigs flexs (Left freshVar:forbs) (Right (f1',g1'):pairs)
                   --fla -> fla $ undefined
 | not (isRigidFormula rigids f1) && isRigidFormula rigids f2 =
    -- NOTE: projection case never happens. only imitation case
    let (bindings, flexs') = unifyFormulasAuxFlexRigid sigs flexs forbs f1 f2
        flexPvar = predicateFormToPredicate f1
        newFlexs = delete (Right flexPvar) flexs++flexs'
     in unifyAux (bound-1) sigs newFlexs forbs (Right (f1, f2):pairs)
 | isRigidFormula rigids f1 && not (isRigidFormula rigids f2) = unifyAux (bound-1) sigs flexs forbs (Right (f2, f1):pairs)
 | not (isRigidFormula rigids f1) && not (isRigidFormula rigids f2) =
    let x = do i <- findIndex (\pair -> case pair of Right (f1, g1) -> isRigidFormula rigids f1 || isRigidFormula rigids g1
                                                     _ -> False) pairs
               let (h, t) = splitAt i pairs
               return (head t:h ++ tail t)
      in case x of Just pairs' -> unifyAux (bound-1) sigs flexs forbs (pairs' ++ [Right (f1, f2)])
                   -- Nothing means that there is no rigid formula nor rigit term in the pairs.
                   Nothing -> unifyFlexFlex sigs flexs forbs (Right (f1, f2):pairs)
                    
                    -- let knownPreds = concat $ map formulaToPredicates (let (x, y) = unzip ((f, g):pairs) in x++y)
                    --             in concat $ map (uncurry $ unifyAuxFlexFlex knownPreds) (Right (f1, f2):pairs)
 where
    rigids = sigs ++ forbs

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
                   Nothing -> let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
                                  freshVarTerm = VarTerm freshVar
                                  (ts0, ts1) = unzip ((t,t'):pairs)
                                in map (\s -> Left (varTermToVar s, freshVarTerm)) (ts0 ++ ts1)
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
                    let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
                        freshVarTerm = VarTerm freshVar
                        f1 = termSubstitutionInFormula v freshVarTerm f'
                        g1 = termSubstitutionInFormula u freshVarTerm g'
                     in unifyFormulasAux (bound-1) sigs flexs (Left freshVar:forbs) ((f1,g1):pairs)
                   (ExistsForm v f', ExistsForm u g') ->
                    let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
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
        binding = Right (p, Compr newVars comprFla)
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
     in [Right (p1,cmp1), Right (p2,cmp2)]

unifyFlexFlex :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [Either (Term, Term) (Formula, Formula)] -> [Binding]
unifyFlexFlex sigs flexs forbs pairs =
    let knownPvars = rights (sigs ++ flexs ++ forbs)
        knownVars = lefts (sigs ++ flexs ++ forbs)
        freshPvar = predicateVariablesAndArityToFreshPredicateVariable knownPvars 0
        freshVar = variablesToFreshVariable knownVars
     in unifyFlexFlexAux freshVar freshPvar pairs

unifyFlexFlexAux :: Variable -> Predicate -> [Either (Term, Term) (Formula, Formula)] -> [Binding]
unifyFlexFlexAux _ _ [] = []
unifyFlexFlexAux freshVar freshPvar (Left(VarTerm v1, VarTerm v2):pairs) =
    let binding1 = (v1, VarTerm freshVar)
        binding2 = (v2, VarTerm freshVar)
        rest = unifyFlexFlexAux freshVar freshPvar pairs
     in Left binding1:Left binding2:rest
unifyFlexFlexAux freshVar freshPvar (Right(PredForm p1 ts1, PredForm p2 ts2):pairs) =
    let vars1 = replicate (length ts1) (variablesToFreshVariable [freshVar])
        vars2 = replicate (length ts2) (variablesToFreshVariable [freshVar])
        binding1 = (p1, Compr vars1 (PredForm freshPvar []))
        binding2 = (p2, Compr vars2 (PredForm freshPvar []))
        rest = unifyFlexFlexAux freshVar freshPvar pairs
     in Right binding1:Right binding2:rest
