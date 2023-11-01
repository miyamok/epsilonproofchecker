module Proof where
import Syntax
import Data.List
import Data.Maybe
import Axiom
import Debug.Trace

data Rule = K | S | ConjI | ConjE1 | ConjE2 | DisjI1 | DisjI2 | DisjE | C
             | AllE | ExI | AllShift | ExShift | Auto | MP Tag Tag
             | Gen Tag | EFQ | DNE | LEM | Asm deriving (Show, Eq)
type Line = (Formula, Rule, Tag)
type Proof = [(Formula, Rule, Tag)]
type Tag = Maybe String
data ErrorMsg = MPIllReference | MPWrongFormula | NotYetSupported
             | KMismatch | KMalformed | SMismatch | SMalformed | CMalformed
             | MPMismatch | MPMalformed | Malformed deriving (Eq, Show)

lineToFormula :: Line -> Formula
lineToFormula (f, _, _) = f

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

genProofToPremiseIndices :: Proof -> [Int]
genProofToPremiseIndices p
 | length p < 2 = []
 | otherwise = let (genFla, _, _) = last p
                   genFlaKernel = case genFla of (ForallForm v f) -> f
                   prems = map (\s -> let (f, _, _) = s in f) (init p)
                   info = map (\prem -> alphaEqFormula prem genFlaKernel || (not $ null $ simpleFormulaUnification prem genFlaKernel)) prems
                  in map snd (filter (\(x, i) -> x) (zip info [0..]))

checkGen :: Proof -> Int -> Tag -> Maybe ErrorMsg
checkGen p i t =
      let pproof = take (i+1) p
          is = genProofToPremiseIndices pproof
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

-- checkLEM :: Formula -> Bool
-- checkLEM (DisjForm f (NegForm g)) = alphaEqFormula f g
-- checkLEM (DisjForm (NegForm f) g) = alphaEqFormula f g
-- checkLEM _ = False

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

proofAndTagStringToLine :: Proof -> String -> Maybe Line
proofAndTagStringToLine p t = proofAndTagStringToLineAux p t 0

proofAndTagStringToLineAux :: Proof -> String -> Int -> Maybe Line
proofAndTagStringToLineAux p t i
 | i >= length p = Nothing
 | otherwise = let l = p!!i
                   (f, r, t') = l
                   next = proofAndTagStringToLineAux p t (i+1)
               in case t' of Nothing -> next
                             Just s' -> if s' == t then Just l else next

proofAndFormulaToLineIndices :: Proof -> Formula -> Int -> [Int]
proofAndFormulaToLineIndices p f bound = proofAndFormulaToLineIndicesAux p f bound 0

proofAndFormulaToLineIndicesAux :: Proof -> Formula -> Int -> Int -> [Int]
proofAndFormulaToLineIndicesAux p f bound i
 | i < bound = let l = p!!i
                   (f', r', t') = l
                   nx = proofAndFormulaToLineIndicesAux p f bound (i+1)
                  in if alphaEqFormula f' f then i:nx else nx
 | otherwise = []

proofAndConclusionToLineIndices :: Proof -> Formula -> Int -> [Int]
proofAndConclusionToLineIndices p f b = proofAndConclusionToLineIndicesAux p f b 0

proofAndConclusionToLineIndicesAux :: Proof -> Formula -> Int -> Int -> [Int]
proofAndConclusionToLineIndicesAux p concl bound i
 | i < bound = let l = p!!i
                   (f, r, t) = l
                   nx = proofAndConclusionToLineIndicesAux p concl bound (i+1)
                  in case f of (ImpForm g g') -> if alphaEqFormula concl g' then i:nx else nx
                               _ -> nx
 | otherwise = []

checkClaims :: Proof -> [Maybe ErrorMsg]
checkClaims p = checkClaimsAux p 0

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
                              let ml1 = proofAndTagStringToLine (take offset p) s1
                                  ml2 = proofAndTagStringToLine (take offset p) s2
                              in if isNothing ml1 || isNothing ml2
                                    then Just MPIllReference
                                    else do (f1, r1, t1) <- ml1
                                            (f2, r2, t2) <- ml2
                                            checkModusPonens f f1 f2
                        MP Nothing Nothing ->
                              let is = proofAndConclusionToLineIndices p f offset -- line indices with matching conclusion
                                  prems = map (\i -> let (f, r, t) = (p!!i) in case f of (ImpForm g _) -> g) is
                              in if any (not . null) (map (\f -> proofAndFormulaToLineIndices p f offset) prems)
                                     then Nothing
                                     else Just MPMalformed
                        C -> checkC f
                        Asm -> Nothing
                        _ -> Just NotYetSupported

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