module Proof where
import Syntax
import Data.List
import Data.Maybe
import Axiom
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

data Rule = K | S | ConjI | ConjE1 | ConjE2 | DisjI1 | DisjI2 | DisjE | C
             | AllE | ExI | AllShift | ExShift | Auto | MP Tag Tag
             | Gen Tag | EFQ | DNE | LEM | Asm | Ref | Use String deriving (Show, Eq)
type Step = (Formula, Rule, Tag)
type Proof = [Step]
type ProofWithLineNumbers = (Proof, [Int])
type Tag = Maybe String
-- type Tag = NoTag | Expl String | Impl String
type ProofBlock = (Maybe String, Proof, Int) -- name, proof, and the line number offset
type Statement = ([Formula], Formula)
type Lemmas = Map Name Proof

stepToFormula :: Step -> Formula
stepToFormula (f, _, _) = f

checkK :: Formula -> Bool
checkK (ImpForm f (ImpForm _ f')) = alphaEqFormula f f'
checkK _ = False

checkS :: Formula -> Bool
checkS (ImpForm (ImpForm f1 (ImpForm f2 f3)) (ImpForm (ImpForm g1 g2) (ImpForm g3 g4)))
      = alphaEqFormula f1 g1 && alphaEqFormula f1 g3 && alphaEqFormula f2 g2 && alphaEqFormula f3 g4
checkS _ = False

checkC :: Formula -> Bool
checkC = isCriticalFormula

checkConjI :: Formula -> Bool
checkConjI (ImpForm f (ImpForm f' (ConjForm g g'))) = alphaEqFormula f g && alphaEqFormula f' g'
checkConjI _ = False

checkConjE1 :: Formula -> Bool
checkConjE1 (ImpForm (ConjForm f _) g) = alphaEqFormula f g
checkConjE1 _ = False

checkConjE2 :: Formula -> Bool
checkConjE2 (ImpForm (ConjForm _ f) g) = alphaEqFormula f g
checkConjE2 _ = False

checkDisjI1 :: Formula -> Bool
checkDisjI1 (ImpForm f (DisjForm g _)) = alphaEqFormula f g
checkDisjI1 _ = False

checkDisjI2 :: Formula -> Bool
checkDisjI2 (ImpForm f (DisjForm _ g)) = alphaEqFormula f g
checkDisjI2 _ = False

checkDisjE :: Formula -> Bool
checkDisjE (ImpForm (DisjForm f f') (ImpForm (ImpForm f1 g1) (ImpForm (ImpForm f1' g1') f2))) =
      alphaEqFormula f f1 && alphaEqFormula f' f1' && alphaEqFormula g1 f2 && alphaEqFormula g1' f2
checkDisjE _ = False

checkAllE :: Formula -> Bool
checkAllE (ImpForm (ForallForm v f) g) = alphaEqFormula f g || length substs == 1
      where
            vars = nub ([v] ++ formulaToVariables f ++ formulaToVariables g)
            freshvar = variablesToFreshVariable vars
            substs = simpleFormulaUnification f g
checkAllE _ = False

checkExI :: Formula -> Bool
checkExI (ImpForm f (ExistsForm v g)) = alphaEqFormula f g || length substs == 1
      where
            substs = simpleFormulaUnification f g
checkExI _ = False

checkAllShift :: Formula -> Bool
checkAllShift (ImpForm (ForallForm v (ImpForm f g)) (ImpForm f' (ForallForm v' g'))) =
      alphaEqFormula f f' && not (v `elem` formulaToFreeVariables f) &&
            (v == v' || not (v' `elem` formulaToFreeVariables g)) &&
            alphaEqFormula g' (termSubstitutionInFormula v (VarTerm v') g)
checkAllShift _ = False

checkExShift :: Formula -> Bool
checkExShift (ImpForm (ForallForm v (ImpForm f g)) (ImpForm (ExistsForm v' f') g')) =
      alphaEqFormula g g' && not (v `elem` formulaToFreeVariables g) &&
            (v == v' || not (v' `elem` formulaToFreeVariables f)) &&
            alphaEqFormula f' (termSubstitutionInFormula v (VarTerm v') f)

checkGen :: Proof -> Bool
checkGen p = let (ForallForm genVar genFlaKernel, _, _) = last p
                 asmFlas = proofToAssumptionFormulas p
                 asmFreeVars = concat $ map formulaToFreeVariables asmFlas
                 is = proofInGenFormToPremiseIndices p
             in if null is then False
                  else let (preFla, _, _) = p!!last is
                           substs = filter (\(x,y) -> case y of VarTerm v -> True; _ -> False) (simpleFormulaUnification genFlaKernel preFla)
                        in if null substs && alphaEqFormula genFlaKernel (preFla)
                              then not (genVar `elem` asmFreeVars)
                              else if length substs == 1
                                    then let (VarTerm x) = fst (head substs) in not (x `elem` asmFreeVars)
                                    else False

checkModusPonens :: Formula -> Formula -> Formula -> Bool
checkModusPonens f g1 g2 = checkModusPonensAux f g1 g2 || checkModusPonensAux f g2 g1

checkModusPonensAux :: Formula -> Formula -> Formula -> Bool
checkModusPonensAux f (ImpForm g1 g2) g3 = alphaEqFormula g1 g3 && alphaEqFormula f g2
checkModusPonensAux _ _ _ = False

checkDNE :: Formula -> Bool
checkDNE (ImpForm (ImpForm (ImpForm f (PredForm Falsum [])) (PredForm Falsum [])) g) = alphaEqFormula f g
checkDNE _ = False

checkEFQ :: Formula -> Bool
checkEFQ (ImpForm (PredForm Falsum ts) f) = True
checkEFQ _ = False

checkAuto :: Formula -> [Formula] -> Bool
checkAuto f asms = undefined

proofToAssumptionFormulas :: Proof -> [Formula]
proofToAssumptionFormulas [] = []
proofToAssumptionFormulas (l:ls) = let (f, r, t) = l
                                       nx = proofToAssumptionFormulas ls
                                    in case r of Asm -> f:nx
                                                 _ -> nx

proofToStatement :: Proof -> Statement
proofToStatement p = (proofToAssumptionFormulas p, proofToConclusion p)

proofAndTagStringToIndices :: Proof -> String -> [Int]
proofAndTagStringToIndices p s = proofAndTagStringToIndicesAux p s 0

proofAndTagStringToIndicesAux :: Proof -> String -> Int -> [Int]
proofAndTagStringToIndicesAux p s i
 | i >= length p = []
 | otherwise = let (f, _, t) = p!!i
                   nx = proofAndTagStringToIndicesAux p s (i+1)
                in case t of Nothing -> nx
                             Just s' -> if s'==s then i:nx else nx

proofAndTagStringToStep :: Proof -> String -> Maybe Step
proofAndTagStringToStep p t = proofAndTagStringToStepAux p t 0

proofAndTagStringToStepAux :: Proof -> String -> Int -> Maybe Step
proofAndTagStringToStepAux p t i
 | i >= length p = Nothing
 | otherwise = let l = p!!i
                   (f, r, t') = l
                   next = proofAndTagStringToStepAux p t (i+1)
               in case t' of Nothing -> next
                             Just s' -> if s' == t then Just l else next

proofAndFormulaToStepIndices :: Proof -> Formula -> Int -> [Int]
proofAndFormulaToStepIndices p f bound = proofAndFormulaToStepIndicesAux p f bound 0

proofAndFormulaToStepIndicesAux :: Proof -> Formula -> Int -> Int -> [Int]
proofAndFormulaToStepIndicesAux p f bound i
 | i < bound = let l = p!!i
                   (f', r', t') = l
                   nx = proofAndFormulaToStepIndicesAux p f bound (i+1)
                  in if alphaEqFormula f' f then i:nx else nx
 | otherwise = []

proofAndMPConclusionToStepIndices :: Proof -> Formula -> [Int]
proofAndMPConclusionToStepIndices p f = proofAndMPConclusionToStepIndicesAux p f 0

proofAndMPConclusionToStepIndicesAux :: Proof -> Formula -> Int -> [Int]
proofAndMPConclusionToStepIndicesAux p concl i
 | i < length p = let l = p!!i
                      (f, r, t) = l
                      nx = proofAndMPConclusionToStepIndicesAux p concl (i+1)
                  in case f of (ImpForm g g') -> if alphaEqFormula concl g' then i:nx else nx
                               _ -> nx
 | otherwise = []

proofInMPFormToMPPremisesIndices :: Proof -> [(Int, Int)]
proofInMPFormToMPPremisesIndices p = proofInMPFormToMPPremisesIndicesAux p concl 0
      where (concl, MP _ _, t) = last p

proofInMPFormToMPPremisesIndicesAux :: Proof -> Formula -> Int -> [(Int, Int)]
proofInMPFormToMPPremisesIndicesAux p concl i
 | i < length p = let (f, r, t) = p!!i
                      nx = proofInMPFormToMPPremisesIndicesAux p concl (i+1)
                  in case f of (ImpForm g g') ->
                                 if alphaEqFormula concl g'
                                    then let js = proofAndFormulaToStepIndices p g (length p)
                                    in map (\j -> (i, j)) js ++ nx
                                    else nx
                               _ -> nx
 | otherwise = []

proofInMPFormToMPPremisesSteps :: Proof -> [(Step, Step)]
proofInMPFormToMPPremisesSteps p = map (\(i,j) -> (p!!i, p!!j)) (proofInMPFormToMPPremisesIndices p)

proofInMPFormToMPPrinciplePremiseFormulas :: Proof -> [Formula]
proofInMPFormToMPPrinciplePremiseFormulas p = let (concl, _, _) = last p
                                                  is = proofAndMPConclusionToStepIndices p concl
                                                in map (\i -> let (f, _, _) = p!!i in f) is

proofInGenFormToPremiseIndices :: Proof -> [Int]
proofInGenFormToPremiseIndices p
 | length p < 2 = []
 | otherwise = let (genFla, _, _) = last p
                   genFlaKernel = case genFla of (ForallForm v f) -> f
                   prems = map (\s -> let (f, _, _) = s in f) (init p)
                   info = map (\prem -> alphaEqFormula prem genFlaKernel || (not $ null $ simpleFormulaUnification prem genFlaKernel)) prems
                  in map snd (filter (\(x, i) -> x) (zip info [0..]))

-- Note that this function doesn't check Auto, simply saying it is correct.
checkProof :: Proof -> Lemmas -> Bool
checkProof p lemma = foldl (\ x i -> x && cs!!i) (last cs) deps
      where cs = checkClaims p lemma
            deps = proofToDependency p

checkUse :: Formula -> [Formula] -> Statement -> Bool
checkUse goalFla goalAsmFlas (lemmaAsmFlas, lemmaGoalFla) = isUnifiableGoal && allAsmValid
      where
            sigVars = nub $ concatMap formulaToFreeVariables (goalFla:goalAsmFlas)
            sigPvars = nub $ concatMap formulaToPredicateVariables (goalFla:goalAsmFlas)
            sigs = map Left sigVars++map Right sigPvars
            lemmaStatementFormula = formulasToImpFormula (lemmaAsmFlas ++ [lemmaGoalFla])
            (Right renamedLemmaStatementFla, freshVarAndPvars) = termOrFormToRenamedTermOrFormAndFreshVarAndPvarList sigs (Right lemmaStatementFormula)
            flas = impFormulaAndNumberToFormulas renamedLemmaStatementFla (length lemmaAsmFlas)
            renamedAsmFlas = init flas
            renamedLemmaGoalFla = last flas
            flexVars = formulaToFreeVariables renamedLemmaStatementFla
            flexPvars = formulaToPredicateVariables renamedLemmaStatementFla
            flexs = map Left flexVars ++ map Right flexPvars
            isUnifiableGoal = unify sigs flexs [] [Right (renamedLemmaGoalFla, goalFla)]
            allAsmValid = all (\lemmaAsmFla -> any (\goalAsmFla -> unify sigs flexs [] [Right (lemmaAsmFla, goalAsmFla)]) goalAsmFlas) lemmaAsmFlas
            --asmValid = all (\lemmaAsmFla -> any (alphaEqFormula lemmaAsmFla) goalAsmFlas) lemmaAsmFlas

checkRef :: Formula -> [Formula] -> Bool
checkRef f = any (alphaEqFormula f)

-- Note that this function doesn't check Auto, simply saying it is correct.
checkClaims :: Proof -> Lemmas -> [Bool]
checkClaims = checkClaimsAux 0

-- Note that this function doesn't check Auto, simply saying it is correct.
checkClaimsAux :: Int -> Proof -> Lemmas -> [Bool]
checkClaimsAux offset p lemmas = if length p <= offset
      then []
      else c:checkClaimsAux (offset+1) p lemmas where
            c = case p!!offset of
                  (f, r, t) -> case r of
                        K -> checkK f
                        S -> checkS f
                        Auto -> True -- automated prover will be applied later
                        ConjE1 -> checkConjE1 f
                        ConjE2 -> checkConjE2 f
                        ConjI -> checkConjI f
                        DisjI1 -> checkDisjI1 f
                        DisjI2 -> checkDisjI2 f
                        DisjE -> checkDisjE f
                        EFQ -> checkEFQ f
                        DNE -> checkDNE f
                        AllE -> checkAllE f
                        ExI -> checkExI f
                        AllShift -> checkAllShift f
                        ExShift -> checkExShift f
                        --Gen Nothing -> checkGen p offset Nothing
                        Gen Nothing -> checkGen (take (offset+1) p)
                        MP (Just s1) (Just s2) ->
                              let mb = (do l1 <- proofAndTagStringToStep (take offset p) s1
                                           l2 <- proofAndTagStringToStep (take offset p) s2
                                           let (f1, r1, t1) = l1
                                               (f2, r2, t2) = l2
                                           return (checkModusPonens f f1 f2))
                              in fromMaybe False mb
                        MP Nothing Nothing ->
                              let is = proofAndMPConclusionToStepIndices (take offset p) f -- Step indices with matching conclusion
                                  prems = map (\i -> let (f, r, t) = (p!!i) in case f of (ImpForm g _) -> g) is
                              in any (not . null) (map (\f -> proofAndFormulaToStepIndices p f offset) prems)
                        C -> checkC f
                        Asm -> True
                        Use lname -> let asmFlas = proofToAssumptionFormulas (take (offset+1) p)
                                      in checkUse f asmFlas (proofToStatement (lemmas Map.! lname))
                        Ref -> let asmFlas = proofToAssumptionFormulas (take (offset+1) p)
                                    in checkRef f asmFlas
                        _ -> False

--- this is a stub.  to remove it?
proofToDependency :: Proof -> [Int]
proofToDependency p = [0..length p-1]

proofToDependencyAux :: Proof -> Int -> [Int]
proofToDependencyAux p i = case p!!i of
      (f, r, t) -> case r of
                  MP Nothing Nothing -> []
                  Gen Nothing -> []
                  K -> []
                  S -> []
                  C -> []
                  ConjE1 -> []
                  ConjE2 -> []
                  ConjI -> []
                  Asm -> []
                  _ -> []

stepToUntaggedStep :: Step -> Step
stepToUntaggedStep (f, MP _ _, _) = (f, MP Nothing Nothing, Nothing)
stepToUntaggedStep (f, Gen _, _) = (f, Gen Nothing, Nothing)
stepToUntaggedStep (f, r, _) = (f, r, Nothing)

proofToUntaggedProof :: Proof -> Proof
proofToUntaggedProof = map stepToUntaggedStep

readProof :: String -> IO [String]
readProof filename = do ls <- fmap lines (readFile filename)
                        return ls

proofToConclusion :: Proof -> Formula
proofToConclusion (s:p) = let (f, _, _) = last (s:p) in f

proofToAsms :: Proof -> Proof
proofToAsms p = filter (\(f, r, t) -> r == Asm) p

proofToNonAsms :: Proof -> Proof
proofToNonAsms p = filter (\(f, r, t) -> r /= Asm) p

isProofWithAuto :: Proof -> Bool
isProofWithAuto p = not (null (proofToAutoStepFormulas p))

proofToAutoStepFormulas :: Proof -> [Formula]
proofToAutoStepFormulas [] = []
proofToAutoStepFormulas ((f, Auto, _):p) = f:proofToAutoStepFormulas p
proofToAutoStepFormulas (_:p) = proofToAutoStepFormulas p

formulaToIdentityProof :: Formula -> Proof
formulaToIdentityProof f =
      let f' = ImpForm f f
      in [(makeSFormula f f' f, S, Nothing),
          (makeKFormula f f', K, Nothing),
          (ImpForm (ImpForm f f') f', MP Nothing Nothing, Nothing),
          (makeKFormula f f, K, Nothing),
          (f', MP Nothing Nothing, Nothing)]

deductionAsm :: Formula -> Step -> Proof
deductionAsm f (g, _, t)
 | alphaEqFormula f g = formulaToIdentityProof f
 | otherwise = [(ImpForm g (ImpForm f g), K, Nothing), (ImpForm f g, MP Nothing Nothing, Nothing)]

deductionBase :: Proof -> Proof
deductionBase p = let asmSteps = proofToAsms p
                      (concl, r, t) = last p
                  in case r of Asm -> init asmSteps ++ formulaToIdentityProof concl
                               _ -> let l = last asmSteps
                                        (lastAsmFla, r', t') = l
                                        newconcl = ImpForm lastAsmFla concl
                                   in init asmSteps ++ [(concl, r, t),
                                                        (ImpForm concl newconcl, K, Nothing),
                                                        (newconcl, MP Nothing Nothing, Nothing)]

deduction :: Proof -> Proof
deduction p
 | null asmProof = p
 | otherwise = deduction $ deductionOnce p
 where
      asmProof = proofToAsms p

deductionOnce :: Proof -> Proof
deductionOnce [] = []
deductionOnce p
 | null asmProof = p
 | otherwise = let (_, r, _) = last p in if r == Asm then deductionBase p
                                                     else deductionAux asmProof nonAsmProof
 where
      asmProof = proofToAsms p
      nonAsmProof = proofToNonAsms p

deductionAux :: Proof -> Proof -> Proof
deductionAux asmProof [] = let initAsms = init asmProof
                               (asmFla, Asm, _) = last asmProof
                           in initAsms ++ concat (map (deductionAsm asmFla) asmProof)
deductionAux asmProof nonAsmProof =
      let (concl, r, _) = last nonAsmProof
          (asmFla, _, t) = last asmProof
          wholeProof = asmProof ++ nonAsmProof
          ihProof = deductionAux asmProof (init nonAsmProof)
          ihAsmProof = proofToAsms ihProof
          ihNonAsmProof = proofToNonAsms ihProof
      in init asmProof ++ ihNonAsmProof ++ case r of
                      MP Nothing Nothing ->
                        let mPIndeces = proofInMPFormToMPPremisesIndices wholeProof
                            (i,j) = head mPIndeces
                            (principleFla, _, _) = wholeProof!!i
                            (subFla, _, _) = wholeProof!!j
                            f1 = ImpForm asmFla principleFla
                            f2 = ImpForm asmFla subFla
                            f3 = ImpForm asmFla concl
                        in [(ImpForm f1 (ImpForm f2 f3), S, Nothing),
                            (ImpForm f2 f3, MP Nothing Nothing, Nothing),
                            (f3, MP Nothing Nothing, Nothing)]
                      MP t t' -> undefined
                      Gen Nothing ->
                        let i = last $ proofInGenFormToPremiseIndices wholeProof
                            (ForallForm var kernel) = concl
                            newPrem = ForallForm var (ImpForm asmFla kernel)
                            newConcl = ImpForm asmFla concl
                        in [(ForallForm var (ImpForm asmFla kernel), Gen Nothing, Nothing),
                            (ImpForm newPrem newConcl, AllShift, Nothing),
                            (newConcl, MP Nothing Nothing, Nothing)]
                      Gen _ -> undefined
                      Ref -> if alphaEqFormula concl asmFla then []
                             else deductionAsm asmFla (last nonAsmProof)
                      _ -> deductionBase (asmProof ++ nonAsmProof) -- case for axioms

isPredicateCalculusRule :: Rule -> Bool
isPredicateCalculusRule AllE = True
isPredicateCalculusRule ExI = True
isPredicateCalculusRule AllShift = True
isPredicateCalculusRule ExShift = True
isPredicateCalculusRule (Gen _) = True
isPredicateCalculusRule _ = False

isPredicateCalculusProof :: Proof -> Bool
isPredicateCalculusProof = any (\(_, r, _) -> isPredicateCalculusRule r)

isEpsilonCalculusProof :: Proof -> Bool
isEpsilonCalculusProof = any (\(_, r, _) -> r == C)

isElementaryCalculusProof :: Proof -> Bool
isElementaryCalculusProof p = not (isEpsilonCalculusProof p || isPredicateCalculusProof p)

proofToProofWithoutDetour :: Proof -> Proof
proofToProofWithoutDetour [] = []
proofToProofWithoutDetour ((f, r, _):ls)
 | alphaEqFormula f f' = [(f, r, Nothing)]
 | otherwise = (f, r, Nothing):proofToProofWithoutDetour (filter (\(g, _, _) -> not (alphaEqFormula f g)) ls)
      where
            (f', _, _) = last ls

emptyLemmas :: Map String Proof
emptyLemmas = Map.empty

proofAndLemmasToInstantiatedProof :: Proof -> Lemmas -> Proof
proofAndLemmasToInstantiatedProof [] _ = []
proofAndLemmasToInstantiatedProof ((f, Use name, _):ls) lemmas =
      proofToNonAsms (lemmas Map.! name) ++ proofAndLemmasToInstantiatedProof ls lemmas
proofAndLemmasToInstantiatedProof (l:ls) lemmas = l:proofAndLemmasToInstantiatedProof ls lemmas
