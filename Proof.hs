module Proof where
import Syntax
import Data.List
import Data.Maybe
import Axiom
import Debug.Trace

-- data Claim = K Formula | S Formula | ConjI Formula | ConjE1 Formula | ConjE2 Formula
--              | DisjI1 Formula | DisjI2 Formula | DisjE Formula | Crit Formula
--              | AllE Formula | ExI Formula | QShiftAll Formula | QShiftEx Formula
--              | Auto Formula | MPIndexed Formula Index Index | MP Formula
--              | GenIndexed Formula | Gen Formula | EFQ Formula | DNE Formula | LEM Formula
--              | Asm Formula deriving (Eq)
data Rule = K | S | ConjI | ConjE1 | ConjE2 | DisjI1 | DisjI2 | DisjE | C
             | AllE | ExI | QShiftAll | QShiftEx | Auto | MP Tag Tag
             | GenTagged Tag | Gen | EFQ | DNE | LEM | Asm deriving (Show, Eq)
type Line = (Formula, Rule, Tag)
type Proof = [(Formula, Rule, Tag)]
type Tag = Maybe String
data ErrorMsg = MPIllReference | MPWrongFormula | NotYetSupported
             | KMismatch | KMalformed | SMismatch | SMalformed | CMalformed
             | MPMismatch | MPMalformed deriving (Eq, Show)

--instance Show Claim where show = claimToString
-- claimToFormula :: Claim -> Formula
-- claimToFormula (K f) = f
-- claimToFormula (S f) = f
-- claimToFormula (MPIndexed f i j) = f

lineToFormula :: Line -> Formula
lineToFormula (f, _, _) = f

-- claimToString :: Claim -> String
-- claimToString (K f) = show f ++ " by " ++ "K"
-- claimToString (S f) = show f ++ " by " ++ "S"
-- claimToString (MPIndexed f i j) = show f ++ " by MP " ++ show i ++ "," ++ show j
-- claimToString (Crit f) = show f ++ " by C"
-- claimToString _ = ""

-- proofToString :: Proof -> String
-- -- proofToString p = concat (map claimToString p)
-- proofToString p = unlines (zipWith (\ n c -> show n ++ " " ++ claimToString c) [0..] p)

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

checkModusPonens :: Formula -> Formula -> Formula -> Maybe ErrorMsg
checkModusPonens f g1 g2
 | checkModusPonensAux f g1 g2 = Nothing
 | checkModusPonensAux f g2 g1 = Nothing
 | otherwise = Just MPMalformed

checkModusPonensAux :: Formula -> Formula -> Formula -> Bool
checkModusPonensAux f (ImpForm g1 g2) g3 = alphaEqFormula g1 g3 && alphaEqFormula f g2
checkModusPonensAux _ _ _ = False

checkDNE :: Formula -> Bool
checkDNE (ImpForm (NegForm (NegForm f)) g) = alphaEqFormula f g
checkDNE _ = False

checkEFQ :: Formula -> Bool
checkEFQ (ImpForm (PredForm Falsum ts) f) = True
checkEFQ _ = False

checkLEM :: Formula -> Bool
checkLEM (DisjForm f (NegForm g)) = alphaEqFormula f g
checkLEM (DisjForm (NegForm f) g) = alphaEqFormula f g
checkLEM _ = False

proofToAssumptionFormulas :: Proof -> [Formula]
proofToAssumptionFormulas [] = []
proofToAssumptionFormulas (l:ls) = let (f, r, t) = l
                                       nx = proofToAssumptionFormulas ls
                                    in case r of Asm -> f:nx
                                                 _ -> nx

proofAndTagToLine :: Proof -> String -> Int -> Maybe Line
proofAndTagToLine p t bound = proofAndTagToLineAux p t bound 0

proofAndTagToLineAux :: Proof -> String -> Int -> Int -> Maybe Line
proofAndTagToLineAux p t bound i
 | i < bound = let l = p!!i
                   (f, r, t') = l
                   next = proofAndTagToLineAux p t bound (i+1)
               in case t' of Nothing -> next
                             Just s' -> if s' == t then Just l else next
 | otherwise = Nothing

proofAndFormulaToLineIndex :: Proof -> Formula -> Int -> Maybe Int
proofAndFormulaToLineIndex p f bound = proofAndFormulaToLineIndexAux p f bound 0

proofAndFormulaToLineIndexAux :: Proof -> Formula -> Int -> Int -> Maybe Int
proofAndFormulaToLineIndexAux p f bound i
 | i < bound = let l = p!!i
                   (f', r', t') = l
                  in if alphaEqFormula f' f then Just i else proofAndFormulaToLineIndexAux p f bound (i+1)
 | otherwise = Nothing

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

-- checkClaimsAux :: Proof -> Int -> [Maybe ErrorMsg]
-- checkClaimsAux p offset
--       | length p > offset = c:checkClaimsAux p (offset+1) where
--             c = case p!!offset of
--                   (f, r, t) -> case r of
--                         K -> checkK f
--                         S -> checkS f
--                         MP Nothing Nothing -> checkModusPonens f (ImpForm f f) f
--                         -- MPIndexed f i j -> if i<offset && j<offset
--                         --       then checkModusPonens f (lineToFormula (p!!i)) (lineToFormula (p!!j))
--                         --       else Just MPIndexOutOfBound
--                         C -> checkC f
--                         _ -> Just NotYetSupported

checkClaimsAux p offset = if length p <= offset
      then []
      else c:checkClaimsAux p (offset+1) where
            c = case p!!offset of
                  (f, r, t) -> case r of
                        K -> checkK f
                        S -> checkS f
                        MP (Just s1) (Just s2) ->
                              -- Should be improved.  Brief coding possible.
                              -- simple do construction does not work; even if ml1 or ml2 is Nothing, the final outcome is not always Nothing.
                              let ml1 = proofAndTagToLine p s1 offset
                                  ml2 = proofAndTagToLine p s2 offset
                              in if isNothing ml1 || isNothing ml2
                                    then Just MPIllReference
                                    else do (f1, r1, t1) <- ml1
                                            (f2, r2, t2) <- ml2
                                            checkModusPonens f f1 f2
                        MP Nothing Nothing ->
                              let is = proofAndConclusionToLineIndices p f offset -- line indices with matching conclusion
                                  prems = map (\i -> let (f, r, t) = (p!!i) in case f of (ImpForm g _) -> g) is
                              in if any isJust (map (\f -> proofAndFormulaToLineIndex p f offset) prems)
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