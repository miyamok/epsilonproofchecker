module Axiom where
import Syntax
import Utils
import Data.List (nubBy, nub, findIndex, findIndices, splitAt, delete, intersect)
import Data.Maybe (catMaybes)
import Data.Either
import Data.Tree
import Debug.Trace

type VarOrPvar = Either Variable Predicate
type TermOrForm = Either Term Formula
type Binding = Either (Variable, Term) (Predicate, Comprehension)
type UnificationPair = Either (Term, Term) (Formula, Formula)
type UnificationTree = Tree ([VarOrPvar], [VarOrPvar], [VarOrPvar], [UnificationPair], [Binding])

unificationBound :: Int
unificationBound = 100

emptyUnificationNode :: Tree ([VarOrPvar], [VarOrPvar], [VarOrPvar], [UnificationPair], [Binding])
emptyUnificationNode = Node ([], [], [], [], []) []

isCriticalFormula :: Formula -> Bool
isCriticalFormula (ImpForm premise conclusion) = any (alphaEqFormula conclusion) concl'
    where
        epsKernels = catMaybes $ map epsTermToKernel (formulaToSubterms conclusion)
        substs = map (\kernel -> simpleFormulaUnification premise kernel) epsKernels
        infos = filter (\(subst, epsKernel) -> length subst == 1) (zip substs epsKernels)
        concl' = map (\pair -> let ([(VarTerm v, t)], f) = pair in epsTranslation $ ExistsForm v f) infos
isCriticalFormula _ = False

bindingAndTermToSubstitutedTerm :: Binding -> Term -> Term
bindingAndTermToSubstitutedTerm (Left (v, t)) t' = termSubstitutionInTerm v t t'

bindingsAndTermToSubstitutedTerm :: [Binding] -> Term -> Term
bindingsAndTermToSubstitutedTerm [] t = t
bindingsAndTermToSubstitutedTerm (b:bs) t = bindingsAndTermToSubstitutedTerm bs (bindingAndTermToSubstitutedTerm b t)

bindingAndFormulaToSubstitutedFormula :: Binding -> Formula -> Formula
bindingAndFormulaToSubstitutedFormula (Left (v, t)) f = termSubstitutionInFormula v t f
bindingAndFormulaToSubstitutedFormula (Right (p, c)) f = formulaSubstitutionInFormula p c f

bindingsAndFormulaToSubstitutedFormula :: [Binding] -> Formula -> Formula
bindingsAndFormulaToSubstitutedFormula [] f = f
bindingsAndFormulaToSubstitutedFormula (b:bs) f = bindingsAndFormulaToSubstitutedFormula bs (bindingAndFormulaToSubstitutedFormula b f)

bindingAndTermOrFormulaToSubstitutedTermOrFormula :: Binding -> Either Term Formula -> Either Term Formula
bindingAndTermOrFormulaToSubstitutedTermOrFormula binding (Left t) = Left (bindingAndTermToSubstitutedTerm binding t)
bindingAndTermOrFormulaToSubstitutedTermOrFormula binding (Right f) = Right (bindingAndFormulaToSubstitutedFormula binding f)

bindingsAndTermOrFormulaToSubstitutedTermOrFormula :: [Binding] -> Either Term Formula -> Either Term Formula
bindingsAndTermOrFormulaToSubstitutedTermOrFormula [] x = x
bindingsAndTermOrFormulaToSubstitutedTermOrFormula (b:bs) x =
    bindingsAndTermOrFormulaToSubstitutedTermOrFormula bs (bindingAndTermOrFormulaToSubstitutedTermOrFormula b x)

bindingAndPairToSubstitutedPair :: Binding -> Either (Term, Term) (Formula, Formula) -> Either (Term, Term) (Formula, Formula)
bindingAndPairToSubstitutedPair b (Left (t, s)) = Left (bindingAndTermToSubstitutedTerm b t, bindingAndTermToSubstitutedTerm b s)
bindingAndPairToSubstitutedPair b (Right (f, g)) = Right (bindingAndFormulaToSubstitutedFormula b f, bindingAndFormulaToSubstitutedFormula b g)

bindingsAndPairToSubstitutedPair :: [Binding] -> Either (Term, Term) (Formula, Formula) -> Either (Term, Term) (Formula, Formula)
bindingsAndPairToSubstitutedPair [] x = x
bindingsAndPairToSubstitutedPair (b:bs) x = bindingsAndPairToSubstitutedPair bs (bindingAndPairToSubstitutedPair b x)

bindingsAndPairsToSubstitutedPairs :: [Binding] -> [Either (Term, Term) (Formula, Formula)] -> [Either (Term, Term) (Formula, Formula)]
bindingsAndPairsToSubstitutedPairs bs xs = map (bindingsAndPairToSubstitutedPair bs) xs

termOrFormToFreeVariables :: TermOrForm -> [Variable]
termOrFormToFreeVariables (Left x) = termToFreeVariables x
termOrFormToFreeVariables (Right x) = formulaToFreeVariables x

termOrFormToVariables :: TermOrForm -> [Variable]
termOrFormToVariables (Left x) = termToVariables x
termOrFormToVariables (Right x) = formulaToVariables x

termOrFormToPredicateVariables :: TermOrForm -> [Predicate]
termOrFormToPredicateVariables (Left x) = termToPredicates x
termOrFormToPredicateVariables (Right x) = formulaToPredicateVariables x

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
simpleTermUnificationAux (ConstTerm c) (ConstTerm c') = []
--simpleTermUnificationAux (AppTerm c ts) (AppTerm c' ts') = concat $ map (uncurry simpleTermUnificationAux) (zip ts ts')
simpleTermUnificationAux (AppTerm t1 t2) (AppTerm s1 s2) =
    let c1:ts = appTermToTerms (AppTerm t1 t2)
        c2:ss = appTermToTerms (AppTerm s1 s2)
      in if c1 == c2 then concat $ map (uncurry simpleTermUnificationAux) (zip ts ss)
                     else []
simpleTermUnificationAux (EpsTerm v f) (EpsTerm v' f') = simpleFormulaUnificationAux g g'
    where
        vars = nub (formulaToVariables f ++ formulaToVariables f' ++ [v, v'])
        freshvarterm = VarTerm (variablesToFreshVariable vars)
        g = termSubstitutionInFormula v freshvarterm f
        g' = termSubstitutionInFormula v' freshvarterm f'

alphaEqTermPair :: (Term, Term) -> (Term, Term) -> Bool
alphaEqTermPair (t1, t2) (s1, s2) = alphaEqTerm t1 s1 && alphaEqTerm t2 s2

alphaEqUnificationPair :: UnificationPair -> Bool
alphaEqUnificationPair (Left (x, y)) = alphaEqTerm x y
alphaEqUnificationPair (Right (x, y)) = alphaEqFormula x y

isRigidTerm :: [VarOrPvar] -> Term -> Bool
isRigidTerm rigidVars (VarTerm v) = Left v `elem` rigidVars
isRigidTerm rigidVars (AppTerm t1 t2) = isRigidTerm rigidVars (head (appTermToTerms (AppTerm t1 t2)))
isRigidTerm _ _ = True

isRigidFormula :: [VarOrPvar] -> Formula -> Bool
isRigidFormula rigidPvars (PredForm Falsum _) = True
isRigidFormula rigidPvars (PredForm Equality _) = True
isRigidFormula rigidPvars (PredForm p _) = Right p `elem` rigidPvars
isRigidFormula _ _ = True

isRigid :: [VarOrPvar] -> Either Term Formula -> Bool
isRigid rigids (Left t) = isRigidTerm rigids t
isRigid rigids (Right f) = isRigidFormula rigids f

isXiUnificationPair :: UnificationPair -> Bool
isXiUnificationPair (Left(EpsTerm v1 f1, EpsTerm v2 f2)) = True
isXiUnificationPair (Right(ForallForm v1 f1, ForallForm v2 f2)) = True
isXiUnificationPair (Right(ExistsForm v1 f1, ExistsForm v2 f2)) = True
isXiUnificationPair _ = False

isRigidRigidUnificationPair :: [VarOrPvar] -> UnificationPair -> Bool
isRigidRigidUnificationPair rigids (Left (x1, x2)) = isRigidTerm rigids x1 && isRigidTerm rigids x2
isRigidRigidUnificationPair rigids (Right (x1, x2)) = isRigidFormula rigids x1 && isRigidFormula rigids x2

isFlexRigidUnificationPair :: [VarOrPvar] -> UnificationPair -> Bool
isFlexRigidUnificationPair rigids (Left (x1, x2)) = not (isRigidTerm rigids x1) && isRigidTerm rigids x2
isFlexRigidUnificationPair rigids (Right (x1, x2)) = not (isRigidFormula rigids x1) && isRigidFormula rigids x2

swapUnificationPair :: UnificationPair -> UnificationPair
swapUnificationPair (Left (x, y)) = Left (y, x)
swapUnificationPair (Right (x, y)) = Right (y, x)

isRigidFlexUnificationPair :: [VarOrPvar] -> UnificationPair -> Bool
isRigidFlexUnificationPair rigids pair = isFlexRigidUnificationPair rigids (swapUnificationPair pair)

isFlexFlexUnificationPair ::  [VarOrPvar] -> UnificationPair -> Bool
isFlexFlexUnificationPair rigids (Left (x1, x2))  = not (isRigidTerm rigids x1) && not (isRigidTerm rigids x2)
isFlexFlexUnificationPair rigids (Right (x1, x2)) = not (isRigidFormula rigids x1) && not (isRigidFormula rigids x2)

unificationTreeToBindingsList :: UnificationTree -> [[Binding]]
unificationTreeToBindingsList (Node (_, _, _, _, bs) []) = [bs]
unificationTreeToBindingsList (Node (_, _, _, _, bs) ts) =
    map (bs ++) (concat $ map unificationTreeToBindingsList ts)

unify :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [UnificationPair] -> Bool
unify sigs flexs forbs [] = True
unify sigs flexs forbs pairs =
    let utree = unifyAux2 unificationBound sigs flexs forbs pairs []
        bindingsList = unificationTreeToBindingsList utree
        unifiedPairsList = map (\bindings -> bindingsAndPairsToSubstitutedPairs bindings pairs) bindingsList
        checkList = map (\unifPairs -> all (==True) $ map alphaEqUnificationPair unifPairs) unifiedPairsList
        ids = findIndices (==True) checkList
      in if null ids then False else True


-- Arguments:
-- Int for the repetition bound which is descreased by each recursive call and the procedure aborts when it became 0.
-- Three [VarOrPvar] are signature variables, flexible variables, and forbidden variables, respectively
-- [UnificationPair] for the list of equation pairs to unify
-- [Binding] for the substitution which was computed in the previous step of the unification procedure
unifyAux2 :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [UnificationPair] -> [Binding] -> UnificationTree
unifyAux2 _ _ _ _ [] _ = emptyUnificationNode
unifyAux2 0 _ _ _ _ _ = emptyUnificationNode
unifyAux2 bound sigs flexs forbs (pair:pairs) bindings
 | alphaEqUnificationPair pair = Node currentNode [unifyAux2 (bound-1) sigs flexs forbs pairs []]
 -- xi case
 | isXiUnificationPair pair =
    let (newForbVar, newPair) = unifyXi sigs flexs forbs pair
      in Node currentNode [unifyAux2 (bound-1) sigs flexs (Left newForbVar:forbs) (newPair:pairs) []]
 -- rigid-rigid case
 | isRigidRigidUnificationPair rigids pair =
    let newPairs = unifyRigidRigid (pair)
     in Node currentNode [unifyAux2 (bound-1) sigs flexs forbs (newPairs ++ pairs) []]
 -- flex-rigid case
 | isFlexRigidUnificationPair rigids pair =
    let (newBindings, oldFlexVar, newFlexVars) = unifyImitation (bound-1) sigs flexs forbs pair
        flexs' = delete oldFlexVar flexs ++ newFlexVars
        pairsImitation = bindingsAndPairsToSubstitutedPairs newBindings (pair:pairs)
        imitationRest = unifyAux2 (bound-1) sigs flexs' forbs pairsImitation newBindings
        imitationNode = Node (sigs, flexs', forbs, pairsImitation, newBindings) [imitationRest]
        projResList = unifyProjection (bound-1) sigs flexs forbs pair
        newFlexsList = map (\(bindings, oldVar, newVars) -> delete oldVar flexs ++ newVars) projResList
        newBindingList = map (\(bindings, oldVar, newVars) -> bindings) projResList
        newPairsList = map (\bs -> bindingsAndPairsToSubstitutedPairs bs (pair:pairs)) newBindingList
        projectionRest = zipWith3 (\newFlxs newBds newPairs -> unifyAux2 (bound-1) sigs newFlxs forbs newPairs newBds)
                            newFlexsList newBindingList newPairsList
        projectionNodes = zipWith3 (\newFlxs newBds newPairs -> Node (sigs, newFlxs, forbs, newPairs, newBds) projectionRest)
                            newFlexsList newBindingList newPairsList
      in Node currentNode (imitationNode:projectionNodes)
 -- rigid-flex case
 | isRigidFlexUnificationPair rigids pair =
    let pair' = swapUnificationPair pair
     in unifyAux2 (bound-1) sigs flexs forbs (pair':pairs) bindings
 -- flex-flex case
 | isFlexFlexUnificationPair rigids pair =
    case findIndex (\ p -> not (isFlexFlexUnificationPair rigids p)) pairs of
        Nothing -> let bindings' = unifyFlexFlex sigs flexs forbs (pair:pairs)
                       pair' = bindingsAndPairsToSubstitutedPairs bindings' (pair:pairs)
                    in Node currentNode [Node (sigs, flexs, forbs, pair', bindings') []]
        Just i -> let nonFlexFlex = pairs !! i
                      (l1, l2) = splitAt i pairs
                      pairs' = nonFlexFlex:init l1++l2++ [pair]
                   in Node currentNode [unifyAux2 (bound-1) sigs flexs forbs pairs' bindings]
 where
    currentNode = (sigs, flexs, forbs, pair:pairs, bindings)
    rigids = sigs ++ forbs

unifyXi :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> UnificationPair -> (Variable, UnificationPair)
unifyXi sigs flexs forbs (Left (EpsTerm v1 f1, EpsTerm v2 f2)) = unifyXiAux sigs flexs forbs (v1, Right f1) (v2, Right f2)
unifyXi sigs flexs forbs (Right (ForallForm v1 f1, ForallForm v2 f2)) = unifyXiAux sigs flexs forbs (v1, Right f1) (v2, Right f2)
unifyXi sigs flexs forbs (Right (ExistsForm v1 f1, ExistsForm v2 f2)) = unifyXiAux sigs flexs forbs (v1, Right f1) (v2, Right f2)
unifyXi sigs flexs forbs (Left (LamTerm vs1 t1, LamTerm vs2 t2)) =
    unifyXiAux sigs flexs forbs (head vs1, Left $ LamTerm (tail vs1) t1) (head vs2, Left $ LamTerm (tail vs2) t2)

unifyXiAux :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> (Variable, TermOrForm) -> (Variable, TermOrForm) -> (Variable, UnificationPair)
unifyXiAux sigs flexs forbs (v1, e1) (v2, e2) =
    case (e1, e2) of (Left t1, Left t2) -> let newt1 = termSubstitutionInTerm v1 freshVarTerm t1
                                               newt2 = termSubstitutionInTerm v2 freshVarTerm t2
                                            in (freshVar, Left (newt1, newt2))
                     (Right f1, Right f2) -> let newf1 = termSubstitutionInFormula v1 freshVarTerm f1
                                                 newf2 = termSubstitutionInFormula v2 freshVarTerm f2
                                            in (freshVar, Right (newf1, newf2))
 where freshVar = variablesToFreshVariable (lefts (sigs++flexs++forbs))
       freshVarTerm = VarTerm freshVar

unifyRigidRigid :: UnificationPair -> [UnificationPair]
unifyRigidRigid (Left (AppTerm t1 t1', AppTerm t2 t2')) =
    let ts1 = appTermToTerms (AppTerm t1 t1')
        ts2 = appTermToTerms (AppTerm t2 t2')
        h1 = head ts1
        h2 = head ts2
      in if alphaEqTerm h1 h2 then map Left (zip (tail ts1) (tail ts2)) else []
unifyRigidRigid (Left (ConstTerm c1, ConstTerm c2)) = []
unifyRigidRigid (Right (PredForm p1 ts1, PredForm p2 ts2)) =
    if p1 == p2 then map Left (zip ts1 ts2) else []
unifyRigidRigid (Right (f, f'))
 | isBiconForm f && isBiconForm f' =
    let (f1, f2) = biconFormToSubFormulas f
        (f1', f2') = biconFormToSubFormulas f'
      in [Right (f1, f1'), Right (f2, f2')]
unifyRigidRigid (Left (LamTerm vs1 t1, LamTerm vs2 t2)) = undefined
unifyRigidRigid _ = []

-- Think what if the value type is of Maybe, since the rhs head must be a signature variable, ow, only projection works.
unifyImitation :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> UnificationPair -> ([Binding], VarOrPvar, [VarOrPvar])
unifyImitation bound sigs flexs forbs (Right(PredForm p ts, f))
 | isPredForm f = let PredForm p' _ = f
                      newFlexVars = variablesAndArityToFreshVariables knownVars comprArity (predicateToArity p')
                      newFlexVarTerms = map VarTerm newFlexVars
                      argTerms = map (\funTerm -> termsToAppTerm (funTerm:comprAbsVarTerms)) newFlexVarTerms
                      newComprKernelFormula = PredForm p' argTerms
                      newCompr = Compr comprAbsVars newComprKernelFormula
                    in ([Right (p, newCompr)], Right p, map Left newFlexVars)
 | isBiconForm f = let newFlexPvars = predicateVariablesAndArityToFreshPredicateVariables knownPvars comprArity 2
                       newSubFormula = PredForm (head newFlexPvars) comprAbsVarTerms
                       newSubFormula' = PredForm (last newFlexPvars) comprAbsVarTerms
                       newComprKernelFormula = case f of (ImpForm _ _) -> ImpForm newSubFormula newSubFormula'
                                                         (ConjForm _ _) -> ConjForm newSubFormula newSubFormula'
                                                         (DisjForm _ _) -> DisjForm newSubFormula newSubFormula'
                    in ([Right(p, Compr comprAbsVars newComprKernelFormula)], Right p, map Right newFlexPvars)
 | isQuantForm f = let (quantVar, kernelFormula) = quantFormToVariableAndFormula f
                       quantVarTerm = VarTerm quantVar
                       newFlexPvar = predicateVariablesAndArityToFreshPredicateVariable knownPvars (comprArity+1)
                       newSubFormula = PredForm newFlexPvar (quantVarTerm:comprAbsVarTerms)
                       newComprKernelFormula = case f of (ForallForm v _) -> ForallForm v newSubFormula
                                                         (ExistsForm v _) -> ExistsForm v newSubFormula
                    in ([Right(p, Compr comprAbsVars newComprKernelFormula)], Right p, [Right newFlexPvar])
 where
    comprArity = length ts
    knownVars = lefts (sigs ++ flexs ++ forbs)
    knownPvars = rights (sigs ++ flexs ++ forbs)
    comprAbsVars = variablesAndArityToFreshVariables knownVars 0 comprArity
    comprAbsVarTerms = map VarTerm comprAbsVars
unifyImitation bound sigs flexs forbs (Left(t, EpsTerm v f)) = undefined
unifyImitation bound sigs flexs forbs (Left(VarTerm v, t)) = ([Left (v, t)], Left v, [])
unifyImitation bound sigs flexs forbs (Left(AppTerm t1 t2, t')) =
    ([Left(leftHeadVar, compr)], Left leftHeadVar, map Left newFlexVars)
    where
        leftTerms = appTermToTerms (AppTerm t1 t2)
        leftHead = head leftTerms
        leftHeadVar = case leftHead of VarTerm v -> v
        leftArgs = tail leftTerms
        (rightHead, rightHeadArity) = case t' of (AppTerm t1' t2') -> let rightTerms = appTermToTerms t'
                                                                        in (head rightTerms, length rightTerms - 1)
                                                 s -> (s, 0)
        knownVars = lefts (sigs ++ flexs ++ forbs)
        knownPvars = rights (sigs ++ flexs ++ forbs)
        comprArity = length leftArgs
        comprAbsVars = variablesAndArityToFreshVariables knownVars 0 comprArity
        comprAbsVarTerms = map VarTerm comprAbsVars
        newFlexVars = variablesAndArityToFreshVariables (knownVars ++ comprAbsVars) comprArity rightHeadArity
        argTerms = map (\funTerm -> termsToAppTerm (funTerm:comprAbsVarTerms)) (map VarTerm newFlexVars)
        compr = LamTerm comprAbsVars (termsToAppTerm (rightHead:argTerms))

unifyProjection :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> UnificationPair -> [([Binding], VarOrPvar, [VarOrPvar])]
unifyProjection bound sigs flexs forbs (Left(AppTerm t1 t2, t')) =
    map (\compr -> ([Left(leftHeadVar, compr)], Left leftHeadVar, map Left newFlexVars)) comprs
    where
        leftTerms = appTermToTerms (AppTerm t1 t2)
        leftHead = head leftTerms
        leftHeadVar = case leftHead of VarTerm v -> v
        leftArgs = tail leftTerms
        (rightHead, rightHeadArity) = case t' of (AppTerm t1' t2') -> let rightTerms = appTermToTerms t'
                                                                        in (head rightTerms, length rightTerms - 1)
                                                 s -> (s, 0)
        knownVars = lefts (sigs ++ flexs ++ forbs)
        knownPvars = rights (sigs ++ flexs ++ forbs)
        comprArity = length leftArgs
        comprAbsVars = variablesAndArityToFreshVariables knownVars 0 comprArity
        comprAbsVarTerms = map VarTerm comprAbsVars
        newFlexVars = variablesAndArityToFreshVariables (knownVars ++ comprAbsVars) comprArity rightHeadArity
        argTerms = map (\funTerm -> termsToAppTerm (funTerm:comprAbsVarTerms)) (map VarTerm newFlexVars)
        comprs = map (\t -> LamTerm comprAbsVars (termsToAppTerm (t:argTerms))) comprAbsVarTerms
unifyProjection bound sigs flexs forbs (Left(t, EpsTerm v f)) = undefined
unifyProjection bound sigs flexs forbs _ = []

unifyFlexFlex :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [UnificationPair] -> [Binding]
unifyFlexFlex sigs flexs forbs pairs =
    let knownPvars = rights (sigs ++ flexs ++ forbs)
        knownVars = lefts (sigs ++ flexs ++ forbs)
        freshPvar = predicateVariablesAndArityToFreshPredicateVariable (knownPvars) 0
        freshVar = variablesToFreshVariable knownVars
     in unifyFlexFlexAux freshVar freshPvar pairs

unifyFlexFlexAux :: Variable -> Predicate -> [UnificationPair] -> [Binding]
unifyFlexFlexAux _ _ [] = []
unifyFlexFlexAux freshVar freshPvar (Left(VarTerm v1, VarTerm v2):pairs) =
    let binding1 = (v1, LamTerm [] $ VarTerm freshVar)
        binding2 = (v2, LamTerm [] $ VarTerm freshVar)
        rest = unifyFlexFlexAux freshVar freshPvar pairs
     in Left binding1:Left binding2:rest
unifyFlexFlexAux freshVar freshPvar (Right(PredForm p1 ts1, PredForm p2 ts2):pairs) =
    let vars1 = replicate (length ts1) (variablesToFreshVariable [freshVar])
        vars2 = replicate (length ts2) (variablesToFreshVariable [freshVar])
        binding1 = (p1, Compr vars1 (PredForm freshPvar []))
        binding2 = (p2, Compr vars2 (PredForm freshPvar []))
        rest = unifyFlexFlexAux freshVar freshPvar pairs
     in Right binding1:Right binding2:rest

renameFreeVarsAndPvarsInTermAndNewVarsAndPvars :: [VarOrPvar] -> Term -> (Term, [VarOrPvar])
renameFreeVarsAndPvarsInTermAndNewVarsAndPvars knowns t = (renamedTerm, map Left freshVars ++ map Right freshPvars)
    where
        fvars = termToFreeVariables t
        pvars = termToPredicates t
        varsToReplace = fvars `intersect` lefts knowns
        pvarsToReplace = pvars `intersect` rights knowns
        freshVars = variablesToFreshVariables (length varsToReplace) (termToVariables t ++ lefts knowns)
        freshPvars = predicateVariablesToFreshPredicateVariables (length pvarsToReplace) (pvars ++ rights knowns)
        varBindings = zipWith (\v v' -> Left (v, VarTerm v')) varsToReplace freshVars
        pvarBindings = zipWith (\p p' -> let absVars = variablesToFreshVariables (predicateToArity p') []
                                             absVarTerms = map VarTerm absVars
                                           in Right (p, Compr absVars (PredForm p' absVarTerms)))
                                pvarsToReplace freshPvars
        renamedTerm = bindingsAndTermToSubstitutedTerm (varBindings ++ pvarBindings) t

termOrFormToRenamedTermOrFormAndFreshVarAndPvarList :: [VarOrPvar] -> TermOrForm -> (TermOrForm, [VarOrPvar])
termOrFormToRenamedTermOrFormAndFreshVarAndPvarList knowns e = (renamedTermOrForm, map Left freshVars ++ map Right freshPvars)
    where
        fvars = termOrFormToFreeVariables e
        pvars = termOrFormToPredicateVariables e
        varsToReplace = fvars `intersect` lefts knowns
        pvarsToReplace = pvars `intersect` rights knowns
        freshVars = variablesToFreshVariables (length varsToReplace) (termOrFormToVariables e ++ lefts knowns)
        freshPvars = predicateVariablesToFreshPredicateVariables (length pvarsToReplace) (pvars ++ rights knowns)
        varBindings = zipWith (\v v' -> Left (v, VarTerm v')) varsToReplace freshVars
        pvarBindings = zipWith (\p p' -> let absVars = variablesToFreshVariables (predicateToArity p') []
                                             absVarTerms = map VarTerm absVars
                                           in Right (p, Compr absVars (PredForm p' absVarTerms)))
                                pvarsToReplace freshPvars
        renamedTermOrForm = case e of Left t -> Left $ bindingsAndTermToSubstitutedTerm (varBindings ++ pvarBindings) t
                                      Right f -> Right $ bindingsAndFormulaToSubstitutedFormula (varBindings ++ pvarBindings) f

-- unifyTerms :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Term, Term)] -> [Binding]
-- unifyTerms = unifyTermsAux unificationBound

-- unifyTermsAux :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [(Term, Term)] -> [Binding]
-- unifyTermsAux 0 _ _ _ _ = []
-- unifyTermsAux bound sigs flexs forbs [] = []
-- unifyTermsAux bound sigs flexs forbs ((t,t'):pairs)
--  | alphaEqTerm t t' = unifyTermsAux (bound-1) sigs flexs forbs pairs
--  | isRigidTerm rigids t && isRigidTerm rigids t' =
--     case (t, t') of (EpsTerm v f, EpsTerm v' f') -> undefined
--                     (AppTerm t1 t2, AppTerm t1' t2') ->
--                         let c:ts = appTermToTerms (AppTerm t1 t2)
--                             c':ts' = appTermToTerms (AppTerm t1' t2')
--                           in if c == c' then unifyTermsAux (bound-1) sigs flexs forbs (zip ts ts' ++ pairs)
--                                         else []
--                     otherewise -> []
--  | isRigidTerm rigids t && not (isRigidTerm rigids t') = unifyTermsAux (bound-1) sigs flexs forbs ((t',t):pairs)
--  | not (isRigidTerm rigids t) && isRigidTerm rigids t' =
--     case t of VarTerm v -> let newPair = (termSubstitutionInTerm v t' t, termSubstitutionInTerm v t' t')
--                                 in unifyTermsAux (bound-1) sigs flexs forbs (newPair:pairs)
--  | not (isRigidTerm rigids t) && not (isRigidTerm rigids t') =
--     let x = do i <- findIndex (\(s, s') -> isRigidTerm rigids s || isRigidTerm rigids s') pairs
--                let (h, t) = splitAt i pairs
--                return (head t:h ++ tail t)
--       in case x of Just pairs' -> unifyTermsAux (bound-1) sigs flexs forbs (pairs' ++ [(t, t')])
--                    Nothing -> let freshVar = variablesToFreshVariable $ lefts (sigs ++ flexs ++ forbs)
--                                   freshVarTerm = VarTerm freshVar
--                                   (ts0, ts1) = unzip ((t,t'):pairs)
--                                 in map (\s -> Left (varTermToVar s, LamTerm [] freshVarTerm)) (ts0 ++ ts1)
--  where
--     rigids = sigs++forbs

-- unificationPairToTerms :: UnificationPair -> [Term]
-- unificationPairToTerms (Left (t1, t2)) = [t1, t2]
-- unificationPairToTerms (Right _) = []

-- unificationPairToFormulas :: UnificationPair -> [Formula]
-- unificationPairToFormulas (Left _) = []
-- unificationPairToFormulas (Right (f1, f2)) = [f1, f2]

-- unificationPairsToTerms :: [UnificationPair] -> [Term]
-- unificationPairsToTerms [] = []
-- unificationPairsToTerms (pair:pairs) = xs ++ unificationPairsToTerms pairs
--     where xs = unificationPairToTerms pair

-- unificationPairsToFormulas :: [UnificationPair] -> [Formula]
-- unificationPairsToFormulas [] = []
-- unificationPairsToFormulas (pair:pairs) = xs ++ unificationPairsToFormulas pairs
--     where xs = unificationPairToFormulas pair

-- unificationPairToVariables :: UnificationPair -> [Variable]
-- unificationPairToVariables (Left (x1, x2)) = concat $ map termToVariables [x1, x2]
-- unificationPairToVariables (Right (x1, x2)) = concat $ map formulaToVariables [x1, x2]

-- unificationPairsToVariables :: [UnificationPair] -> [Variable]
-- unificationPairsToVariables [] = []
-- unificationPairsToVariables (x:xs) = vs ++ unificationPairsToVariables xs
--     where vs = unificationPairToVariables x

-- unifyTermAuxFlexRigid  :: [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> Term -> Term -> ([Binding], [VarOrPvar])
-- unifyTermAuxFlexRigid sigs flexs forbs (VarTerm v) (AppTerm t1 t2) =
--     let c:ts = appTermToTerms (AppTerm t1 t2)
--         arity = length ts
--         knownVars = lefts (sigs ++ flexs ++ forbs)
--         freshVars = variablesToFreshVariables arity knownVars
--         freshVarTerms = map VarTerm freshVars
--         binding = (v, LamTerm [] $ termsToAppTerm (c:freshVarTerms))
--      in ([Left binding], map Left freshVars)
-- unifyTermAuxFlexRigid sigs flexs forbs (VarTerm v) (VarTerm u) =
--     let binding = (v, LamTerm [] $ VarTerm u)
--      in ([Left binding], [])
-- unifyTermAuxFlexRigid sigs flexs forbs (VarTerm v) (ConstTerm c) =
--     let binding = (v, LamTerm [] $ ConstTerm c)
--      in ([Left binding], [])

-- unifyFlexRigidBicon :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [Either (Term, Term) (Formula, Formula)] -> ([Binding], [VarOrPvar])
-- unifyFlexRigidBicon bound sigs flexs forbs [Right (PredForm p ts, g)] =
--     let pArity = length ts
--         rigids = sigs ++ forbs
--         newVars = variablesToFreshVariables pArity []
--         newVarTerms = map VarTerm newVars
--         knownPvars = rights (sigs ++ flexs ++ forbs)
--         newPvars = predicateVariablesAndArityToFreshPredicateVariables (p:knownPvars) 0 2
--         newArgFlas = map (\newPvar -> PredForm newPvar newVarTerms) newPvars
--         comprFla = case g of ImpForm _ _ -> ImpForm (head newArgFlas) (last newArgFlas)
--                              ConjForm _ _ -> ConjForm (head newArgFlas) (last newArgFlas)
--                              DisjForm _ _ -> DisjForm (head newArgFlas) (last newArgFlas)
--         binding = Right (p, Compr newVars comprFla)
--      in ([binding], map Right newPvars)

-- unifyFlexRigidQuant :: Int -> [VarOrPvar] -> [VarOrPvar] -> [VarOrPvar] -> [Either (Term, Term) (Formula, Formula)] -> ([Binding], [VarOrPvar])
-- unifyFlexRigidQuant bound sigs flexs forbs [Right (PredForm p ts, g)] =
--     let knownVars = lefts (sigs ++ flexs ++ forbs)
--         comprhensionAbsVars = variablesToFreshVariables (length ts) knownVars
--         rigids = sigs ++ forbs
--         comprhensionAbsVarTerms = map VarTerm comprhensionAbsVars
--         --newPvars = predicateVariablesAndArityToFreshPredicateVariables (p:rigidPreds ++ flexPvars) gArity
--         --newArgFla = PredForm newPvar []
--         quantVar = case g of ForallForm v _ -> v
--                              ExistsForm v _ -> v
--         newPvarArity = length ts + 1 -- +1 for the quantVar
--         newPvar = predicateVariablesAndArityToFreshPredicateVariable (p:rights (rigids ++ flexs)) newPvarArity
--         maxIdx = maximum (0:map variableToIndex (knownVars ++ concatMap termToVariables ts ++ concatMap termToVariables (formulaToSubterms g)))
--         funVars = map (\i -> Var "_" (i+maxIdx) (length ts+1)) [1..newPvarArity]
--         newPredArgTerms = map (\funVar -> termsToAppTerm (VarTerm funVar:VarTerm quantVar:comprhensionAbsVarTerms)) funVars
--         newKernel = PredForm newPvar newPredArgTerms
--         comprFla = case g of ForallForm v _ -> ForallForm v newKernel
--                              ExistsForm v _ -> ExistsForm v newKernel
--         binding = Right (p, Compr comprhensionAbsVars comprFla)
--      in ([binding], (Right newPvar):(map Left funVars))

