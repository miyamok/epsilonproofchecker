module Proof where
import Syntax
import Data.List
import Data.Maybe
import Axiom
import Debug.Trace

data Rule = K | S | ConjI | ConjE1 | ConjE2 | DisjI1 | DisjI2 | DisjE | C
             | AllE | ExI | AllShift | ExShift | Auto | MP Tag Tag
             | Gen Tag | EFQ | DNE | LEM | Asm deriving (Show, Eq)
type Step = (Formula, Rule, Tag)
type Proof = [(Formula, Rule, Tag)]
type Tag = Maybe String
-- type Tag = NoTag | Expl String | Impl String
data ErrorMsg = MPIllReference | MPWrongFormula | NotYetSupported
             | KMismatch | KMalformed | SMismatch | SMalformed | CMalformed
             | MPMismatch | MPMalformed | Malformed deriving (Eq, Show)

stepToFormula :: Step -> Formula
stepToFormula (f, _, _) = f

checkAuto :: Formula -> Bool
checkAuto f = True

checkK :: Formula -> Maybe ErrorMsg
checkK (ImpForm f1 (ImpForm f2 f3)) = if alphaEqFormula f1 f3 then Nothing else Just KMismatch
checkK _ = Just KMalformed

checkS :: Formula -> Maybe ErrorMsg
checkS (ImpForm (ImpForm f1 (ImpForm f2 f3)) (ImpForm (ImpForm g1 g2) (ImpForm g3 g4)))
      = if alphaEqFormula f1 g1 && alphaEqFormula f1 g3 && alphaEqFormula f2 g2 && alphaEqFormula f3 g4
            then Nothing else Just SMismatch
checkS _ = Just SMalformed

checkC :: Formula -> Maybe ErrorMsg
checkC f = if isCriticalFormula f then Nothing else Just CMalformed

checkConjI :: Formula -> Maybe ErrorMsg
checkConjI (ImpForm f (ImpForm f' (ConjForm g g'))) = if alphaEqFormula f g && alphaEqFormula f' g' then Nothing else Just Malformed
checkConjI _ = Just Malformed

checkConjE1 :: Formula -> Maybe ErrorMsg
checkConjE1 (ImpForm (ConjForm f _) g) = if alphaEqFormula f g then Nothing else Just Malformed
checkConjE1 _ = Just Malformed

checkConjE2 :: Formula -> Maybe ErrorMsg
checkConjE2 (ImpForm (ConjForm _ f) g) = if alphaEqFormula f g then Nothing else Just Malformed
checkConjE2 _ = Just Malformed

checkDisjI1 :: Formula -> Maybe ErrorMsg
checkDisjI1 (ImpForm f (DisjForm g _)) = if alphaEqFormula f g then Nothing else Just Malformed
checkDisjI1 _ = Just Malformed

checkDisjI2 :: Formula -> Maybe ErrorMsg
checkDisjI2 (ImpForm f (DisjForm _ g)) = if alphaEqFormula f g then Nothing else Just Malformed
checkDisjI2 _ = Just Malformed

checkDisjE :: Formula -> Maybe ErrorMsg
checkDisjE (ImpForm (DisjForm f f') (ImpForm (ImpForm f1 g1) (ImpForm (ImpForm f1' g1') f2))) =
      if alphaEqFormula f f1 && alphaEqFormula f' f1' && alphaEqFormula g1 f2 && alphaEqFormula g1' f2
            then Nothing
            else Just Malformed
checkDisjE _ = Just Malformed

checkAllE :: Formula -> Maybe ErrorMsg
checkAllE (ImpForm (ForallForm v f) g) = if length substs == 1 then Nothing else Just Malformed
      where
            vars = nub ([v] ++ formulaToVariables f ++ formulaToVariables g)
            freshvar = variablesToFreshVariable vars
            substs = simpleFormulaUnification f g
checkAllE _ = Just Malformed

checkExI :: Formula -> Maybe ErrorMsg
checkExI (ImpForm f (ExistsForm v g)) = if length substs == 1 then Nothing else Just Malformed
      where
            substs = simpleFormulaUnification f g
checkExI _ = Just Malformed

checkAllShift :: Formula -> Maybe ErrorMsg
checkAllShift (ImpForm (ForallForm v (ImpForm f g)) (ImpForm f' (ForallForm v' g'))) =
      if alphaEqFormula f f' && not (v `elem` formulaToFreeVariables f) &&
            (v == v' || not (v' `elem` formulaToFreeVariables g)) &&
            alphaEqFormula g' (substFormula v (VarTerm v') g)
            then Nothing
            else Just Malformed
checkAllShift _ = Just Malformed

checkExShift :: Formula -> Maybe ErrorMsg
checkExShift (ImpForm (ForallForm v (ImpForm f g)) (ImpForm (ExistsForm v' f') g')) =
      if alphaEqFormula g g' && not (v `elem` formulaToFreeVariables g) &&
            (v == v' || not (v' `elem` formulaToFreeVariables f)) &&
            alphaEqFormula f' (substFormula v (VarTerm v') f)
            then Nothing
            else Just Malformed

proofInGenFormToPremiseIndices :: Proof -> [Int]
proofInGenFormToPremiseIndices p
 | length p < 2 = []
 | otherwise = let (genFla, _, _) = last p
                   genFlaKernel = case genFla of (ForallForm v f) -> f
                   prems = map (\s -> let (f, _, _) = s in f) (init p)
                   info = map (\prem -> alphaEqFormula prem genFlaKernel || (not $ null $ simpleFormulaUnification prem genFlaKernel)) prems
                  in map snd (filter (\(x, i) -> x) (zip info [0..]))

checkGen :: Proof -> Int -> Tag -> Maybe ErrorMsg
checkGen p i t =
      let pproof = take (i+1) p
          is = proofInGenFormToPremiseIndices pproof
          asms = proofToAssumptionFormulas p
          freeVars = concat $ map formulaToFreeVariables asms
          genVar = let (f, t, r) = (p!!i) in case f of (ForallForm v f) -> v
      in if genVar `elem` freeVars then Just Malformed
         else case t of Nothing -> if null is then Just Malformed else Nothing
                        Just s -> if any (`elem` is) (proofAndTagStringToIndices pproof s) then Nothing else Just Malformed

checkModusPonens :: Formula -> Formula -> Formula -> Maybe ErrorMsg
checkModusPonens f g1 g2
 | checkModusPonensAux f g1 g2 = Nothing
 | checkModusPonensAux f g2 g1 = Nothing
 | otherwise = Just MPMalformed

checkModusPonensAux :: Formula -> Formula -> Formula -> Bool
checkModusPonensAux f (ImpForm g1 g2) g3 = alphaEqFormula g1 g3 && alphaEqFormula f g2
checkModusPonensAux _ _ _ = False

checkDNE :: Formula -> Maybe ErrorMsg
checkDNE (ImpForm (ImpForm (ImpForm f (PredForm Falsum [])) (PredForm Falsum [])) g) = if alphaEqFormula f g then Nothing else Just Malformed
checkDNE _ = Just Malformed

checkEFQ :: Formula -> Maybe ErrorMsg
checkEFQ (ImpForm (PredForm Falsum ts) f) = Nothing
checkEFQ _ = Just Malformed

proofToAssumptionFormulas :: Proof -> [Formula]
proofToAssumptionFormulas [] = []
proofToAssumptionFormulas (l:ls) = let (f, r, t) = l
                                       nx = proofToAssumptionFormulas ls
                                    in case r of Asm -> f:nx
                                                 _ -> nx

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
                                                
checkClaims :: Proof -> [Maybe ErrorMsg]
checkClaims p = checkClaimsAux p 0

checkClaimsAux :: [(Formula, Rule, Tag)] -> Int -> [Maybe ErrorMsg]
checkClaimsAux p offset = if length p <= offset
      then []
      else c:checkClaimsAux p (offset+1) where
            c = case p!!offset of
                  (f, r, t) -> case r of
                        K -> checkK f
                        S -> checkS f
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
                        Gen t -> checkGen p offset t
                        MP (Just s1) (Just s2) ->
                              -- Should be improved.  Brief coding possible.
                              -- simple do construction does not work; even if ml1 or ml2 is Nothing, the final outcome is not always Nothing.
                              let ml1 = proofAndTagStringToStep (take offset p) s1
                                  ml2 = proofAndTagStringToStep (take offset p) s2
                              in if isNothing ml1 || isNothing ml2
                                    then Just MPIllReference
                                    else do (f1, r1, t1) <- ml1
                                            (f2, r2, t2) <- ml2
                                            checkModusPonens f f1 f2
                        MP Nothing Nothing ->
                              let is = proofAndMPConclusionToStepIndices (take offset p) f -- Step indices with matching conclusion
                                  prems = map (\i -> let (f, r, t) = (p!!i) in case f of (ImpForm g _) -> g) is
                              in if any (not . null) (map (\f -> proofAndFormulaToStepIndices p f offset) prems)
                                     then Nothing
                                     else Just MPMalformed
                        C -> checkC f
                        Asm -> Nothing
                        _ -> Just NotYetSupported

--proofAndFormulaToMPPremiseIndices :: Proof -> Formula -> 

-- proofToMPPremiseIndices :: Proof -> [(Int, Int)]
-- proofToMPPremiseIndices p = let is = proofAndMPConclusionToLineIndices p
--                                 premFlas = map (\i -> let (f, r, t) = p!!i in formulaInImpFormToPremise f) is
--                              in undefined

proofToDependency :: Proof -> [Int]
--proofToDependency p = proofToDependencyAux p (length p-1)
proofToDependency p = [0..length p-1]

proofToDependencyAux :: Proof -> Int -> [Int]
proofToDependencyAux p i = case p!!i of
      (f, r, t) -> case r of
                  K -> []
                  S -> []
                  C -> []
                  ConjE1 -> []
                  ConjE2 -> []
                  ConjI -> []
                  Asm -> []
--                  MPTagged t1 t2 -> sort $ nub ([j, k] ++ proofToDependencyAux p j ++ proofToDependencyAux p k)
                  _ -> []

checkProof :: Proof -> Bool
checkProof p = foldl (\ x i -> x && isNothing (cs!!i)) (isNothing (last cs)) deps
      where cs = checkClaims p
            deps = proofToDependency p
-- checkProofAux [] offset = []
-- checkProofAux (c:cs) offset = b:checkProofAux cs (offset + 1)
--       where
--             b = case c of
--                   Auto f -> checkAuto f
--                   MPIndexed f i1 i2 -> checkModusPonens f f1 f2
--                         where f1 = 
-- checkFormulasAux (Auto f:cs) offset = checkAuto f:checkFormulasAux cs offset
-- checkFormulasAux ((MPIndexed f i1 i2):cs) offset = checkModusPonens f g1 g2:checkFormulasAux cs offset
--              where n = length cs-1
--                    g1 = case cs!!(n-i1) of
--                              Auto f' -> f'
--                              MPIndexed f' i1' i2' -> f'
--                    g2 = case cs!!(n-i2) of
--                              Auto f' -> f'
--                              MPIndexed f' i1' i2' -> f'

-- checkProofAux :: [Formula] -> Proof -> Bool
-- checkProofAux as (f:fs) = True

-- checkProof :: Proof -> Bool
-- checkProof = checkProofAux []

readProof :: String -> IO [String]
readProof filename = do ls <- fmap lines (readFile filename)
                        return ls

proofToAsms :: Proof -> Proof
proofToAsms p = filter (\(f, r, t) -> r == Asm) p

proofToNonAsms :: Proof -> Proof
proofToNonAsms p = filter (\(f, r, t) -> r /= Asm) p

formulaToIdentityProof :: Formula -> Proof
formulaToIdentityProof f =
      let f' = ImpForm f f
      in [(makeSFormula f f' f, S, Nothing),
          (makeKFormula f f', K, Nothing),
          (ImpForm (ImpForm f f') f', MP Nothing Nothing, Nothing),
          (makeKFormula f f, K, Nothing),
          (f', MP Nothing Nothing, Nothing)]
      -- let f1 = ImpForm f (ImpForm (ImpForm f f) f)
      --     f2 = ImpForm f (ImpForm f f)
      --     f3 = ImpForm f f
      -- in [(ImpForm f1 (ImpForm f2 f3), S, Nothing),
      --     (f1, K, Nothing),
      --     (ImpForm f2 f3, MP Nothing Nothing, Nothing),
      --     (f2, K, Nothing),
      --     (f3, MP Nothing Nothing, Nothing)]

deductionAsm :: Formula -> Step -> Proof
deductionAsm f (g, Asm, t)
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
 | null asmProof = p -- nothing to do
 | null nonAsmProof = deduction $ deductionBase p -- Asm reference is the conclusion of the proof
 | otherwise = deduction $ deductionAux asmProof nonAsmProof
 where
      asmProof = proofToAsms p
      nonAsmProof = proofToNonAsms p

deductionOnce :: Proof -> Proof
deductionOnce p
 | null asmProof = p -- nothing to do
 | null nonAsmProof = deductionBase p -- Asm reference is the conclusion of the proof
 | otherwise = deductionAux asmProof nonAsmProof
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
          ihAsmProof = traceShowId $ proofToAsms ihProof
          ihNonAsmProof = proofToNonAsms ihProof
      in init asmProof ++ ihNonAsmProof ++ case r of --Asm -> init asmProof ++ formulaToIdentityProof concl
                      --              else undefined -- case if Asm appears in the middle of the proof
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
                      _ -> deductionBase (asmProof ++ nonAsmProof) -- case for axioms
