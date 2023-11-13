module Script where
import Data.List(nub, findIndex, findIndices, delete, intersect)
import Data.Maybe(listToMaybe)
import Syntax
import Proof
import Utils
import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

data ScriptLine = ProofLine Int Step | VarDeclareLine Int [VariableDeclaration] | ConstDeclareLine Int [ConstantDeclaration]
 | PredDeclareLine Int [PredicateDeclaration] | EmptyLine Int | ErrorLine Int String | EndProofLine Int (Maybe String)
 | DeductionTransformationLine Int (Maybe Int) (Maybe String) deriving (Show)
type Script = [ScriptLine]
type ScriptBlock = (Script, Int, Maybe String)
type ProofBlock = (Proof, [Int], Maybe String)

scriptToErrorMessage :: Script -> Maybe String
scriptToErrorMessage [] = Just "Empty input"
scriptToErrorMessage ls =
    do i <- findIndex (\l -> case l of ErrorLine i s -> True; _ -> False) ls
       l <- listToMaybe [e | e@(ErrorLine _ _) <- ls]
       s <- case l of ErrorLine _ s -> Just s ; _ -> Nothing
       return ("Error at line " ++ show (i+1) ++ ": " ++ s)

scriptToProof :: Script -> Proof
scriptToProof [] = []
scriptToProof (ProofLine _ x:ls) = x:scriptToProof ls
scriptToProof (_:ls) = scriptToProof ls

scriptToDeclarations :: Script -> Declarations
scriptToDeclarations s = (varDecs, constDecs, predDecs)
 where varDecsLNs = scriptToVariableDeclarationsWithLineIndices s
       varDecs = concat $ map fst varDecsLNs
       constDecsLNs = scriptToConstantDeclarationsWithLineIndices s
       constDecs = concat $ map fst constDecsLNs
       predDecsLNs = scriptToPredicateDeclarationsWithLineIndices s
       predDecs = concat $ map fst predDecsLNs

scriptToVariableDeclarationsWithLineIndices :: Script -> [([VariableDeclaration], Int)]
scriptToVariableDeclarationsWithLineIndices [] = []
scriptToVariableDeclarationsWithLineIndices (VarDeclareLine i ds:ls) = (ds, i):scriptToVariableDeclarationsWithLineIndices ls
scriptToVariableDeclarationsWithLineIndices (_:ls) = scriptToVariableDeclarationsWithLineIndices ls

scriptToConstantDeclarationsWithLineIndices :: Script -> [([ConstantDeclaration], Int)]
scriptToConstantDeclarationsWithLineIndices [] = []
scriptToConstantDeclarationsWithLineIndices (ConstDeclareLine i ds:ls) = (ds, i):scriptToConstantDeclarationsWithLineIndices ls
scriptToConstantDeclarationsWithLineIndices (_:ls) = scriptToConstantDeclarationsWithLineIndices ls

scriptToPredicateDeclarationsWithLineIndices :: Script -> [([PredicateDeclaration], Int)]
scriptToPredicateDeclarationsWithLineIndices [] = []
scriptToPredicateDeclarationsWithLineIndices (PredDeclareLine i ds:ls) = (ds, i):scriptToPredicateDeclarationsWithLineIndices ls
scriptToPredicateDeclarationsWithLineIndices (_:ls) = scriptToPredicateDeclarationsWithLineIndices ls

scriptToInconsistentIdentifierNames :: Script -> [Name]
scriptToInconsistentIdentifierNames s = declarationsToInconsistentIdentifierNames (scriptToDeclarations s)

scriptToConflictingVariableDeclarationsWithLNsDueToDefaultDeclarations :: Script -> [([VariableDeclaration], Int)]
scriptToConflictingVariableDeclarationsWithLNsDueToDefaultDeclarations s
 | null (vnames `intersect` conflictingNames) = []
 | not (null conflictingDefCNames) || not (null conflictingDefPNames) = conflictingVarDecLNs
 | otherwise = []
       where
              conflictingNames = scriptToInconsistentIdentifierNames s
              (vnames, cds, pds) = scriptToDeclarations s
              cnames = map fst cds
              pnames = map fst pds
              conflictingDefCNames = if null cnames then map fst defaultConstants `intersect` vnames else []
              conflictingDefPNames = if null pnames then map fst defaultPredicates `intersect` vnames else []
              conflictingVarDecLNs = filter (\(ds, i) -> not (null (ds `intersect` conflictingNames)))
                                            (scriptToVariableDeclarationsWithLineIndices s)

scriptToConflictingConstantDeclarationsWithLNsDueToDefaultDeclarations :: Script -> [([ConstantDeclaration], Int)]
scriptToConflictingConstantDeclarationsWithLNsDueToDefaultDeclarations s
 | null (cnames `intersect` conflictingNames) = []
 | not (null conflictingDefVNames) || not (null conflictingDefPNames) = conflictingConstDecLNs
 | otherwise = []
       where
              conflictingNames = scriptToInconsistentIdentifierNames s
              (vnames, cds, pds) = scriptToDeclarations s
              cnames = map fst cds
              pnames = map fst pds
              conflictingDefVNames = if null vnames then defaultVariables `intersect` vnames else []
              conflictingDefPNames = if null pnames then map fst defaultPredicates `intersect` vnames else []
              conflictingConstDecLNs = filter (\(ds, i) -> not (null (map fst ds `intersect` conflictingNames)))
                                              (scriptToConstantDeclarationsWithLineIndices s)

scriptToConflictingPredicateDeclarationsWithLNsDueToDefaultDeclarations :: Script -> [([PredicateDeclaration], Int)]
scriptToConflictingPredicateDeclarationsWithLNsDueToDefaultDeclarations s
 | null (pnames `intersect` conflictingNames) = []
 | not (null conflictingDefVNames) || not (null conflictingDefCNames) = conflictingPredDecLNs
 | otherwise = []
       where
              conflictingNames = scriptToInconsistentIdentifierNames s
              (vnames, cds, pds) = scriptToDeclarations s
              cnames = map fst cds
              pnames = map fst pds
              conflictingDefCNames = if null cnames then map fst defaultConstants `intersect` vnames else []
              conflictingDefVNames = if null vnames then defaultVariables `intersect` vnames else []
              conflictingDefPNames = if null pnames then map fst defaultPredicates `intersect` vnames else []
              conflictingPredDecLNs = filter (\(ds, i) -> not (null (map fst ds `intersect` conflictingNames)))
                                              (scriptToPredicateDeclarationsWithLineIndices s)

areConsistentVariableDeclarations :: [VariableDeclaration] -> Bool
areConsistentVariableDeclarations ds = length ds == length (nub ds)

areConsistentConstantDeclarations :: [ConstantDeclaration] -> Bool
areConsistentConstantDeclarations ds = let names = map fst ds
                                           arities = map snd ds
                                       in length ds == length (nub ds) && all (>= 0) arities

areConsistentPredicateDeclarations :: [PredicateDeclaration] -> Bool
areConsistentPredicateDeclarations ds = let names = map fst ds
                                            arities = map snd ds
                                        in length ds == length (nub ds) && all (>= 0) arities

scriptToProofBlocks :: Script -> [(Proof, [Int], Maybe String)]
scriptToProofBlocks = scriptToProofBlocksAux 0 [] [] Nothing emptyLemmas

scriptToProofBlocksAux :: Int -> Proof -> [Int] -> Maybe String -> Lemmas -> Script -> [(Proof, [Int], Maybe String)]
scriptToProofBlocksAux _ [] [] _ lemmas [] = []
scriptToProofBlocksAux _ p is ms lemmas [] = [(p, is, ms)]
scriptToProofBlocksAux i p is _ lemmas (ProofLine _ x:s) = scriptToProofBlocksAux (i+1) (p++[x]) (is++[i]) Nothing lemmas s
scriptToProofBlocksAux i p is _ lemmas (EndProofLine _ mn:s) =
       (p, is, mn):scriptToProofBlocksAux (i+1) [] [] Nothing (case mn of Nothing -> lemmas ; Just n -> Map.insert n p lemmas) s
scriptToProofBlocksAux i p is _ lemmas (DeductionTransformationLine _ mi Nothing:s) =
       (p, is, Nothing):scriptToProofBlocksAux (i+1) dp is' Nothing lemmas s
    where
        p' = proofAndLemmasToInstantiatedProof (proofToUntaggedProof p) lemmas
        dp = case mi of Nothing -> deduction p'; Just i -> iterate deductionOnce p'!!i
        is' = replicate (length dp) (-1)
scriptToProofBlocksAux i p is _ lemmas (ErrorLine _ x:s) = [(p, is, Nothing)]
scriptToProofBlocksAux i p is _ lemmas (_:s) = scriptToProofBlocksAux (i+1) p is Nothing lemmas s

isProofScriptLine :: ScriptLine -> Bool
isProofScriptLine (ProofLine _ _) = True
isProofScriptLine (EndProofLine _ _) = True
isProofScriptLine (DeductionTransformationLine _ _ _) = True
isProofScriptLine _ = False

isDeclarationScriptLine :: ScriptLine -> Bool
isDeclarationScriptLine sl =
       any (\f -> f sl) [isVariableDeclarationScriptLine, isConstantDeclarationScriptLine, isPredicateDeclarationScriptLine]

isVariableDeclarationScriptLine :: ScriptLine -> Bool
isVariableDeclarationScriptLine (VarDeclareLine _ _) = True
isVariableDeclarationScriptLine _ = False

isConstantDeclarationScriptLine :: ScriptLine -> Bool
isConstantDeclarationScriptLine (ConstDeclareLine _ _) = True
isConstantDeclarationScriptLine _ = False

isPredicateDeclarationScriptLine :: ScriptLine -> Bool
isPredicateDeclarationScriptLine (PredDeclareLine _ _) = True
isPredicateDeclarationScriptLine _ = False

scriptToIllegalDeclarationIndex :: Script -> Maybe Int
scriptToIllegalDeclarationIndex s = do fpi <- findIndex isProofScriptLine s
                                       let dis = findIndices isDeclarationScriptLine s
                                           illIs = filter (>fpi) dis
                                        in if null illIs then Nothing else Just (head illIs)

scriptToIllegalDeclarationIndices :: Script -> [Int]
scriptToIllegalDeclarationIndices s = let mfpi = findIndex isProofScriptLine s
                                          dis = findIndices isDeclarationScriptLine s
                                        in case mfpi of Nothing -> []
                                                        Just fpi -> filter (>fpi) dis

scriptToLemmaNameAndIndexList :: Script -> [(String, Int)]
scriptToLemmaNameAndIndexList [] = []
scriptToLemmaNameAndIndexList (EndProofLine i (Just n):ls) = (n, i):scriptToLemmaNameAndIndexList ls
scriptToLemmaNameAndIndexList (_:ls) = scriptToLemmaNameAndIndexList ls

-- scriptToLemmaNameAndIndexListAux :: Int -> Script -> [(String, Int)]
-- scriptToLemmaNameAndIndexListAux _ [] = []
-- scriptToLemmaNameAndIndexListAux i (EndProofLine _ Nothing:ls) = scriptToLemmaNameAndIndexListAux (i+1) ls
-- scriptToLemmaNameAndIndexListAux i (EndProofLine _ (Just n):ls) = (n,i):scriptToLemmaNameAndIndexListAux (i+1) ls
-- scriptToLemmaNameAndIndexListAux i (_:ls) = scriptToLemmaNameAndIndexListAux (i+1) ls

scriptToConflictingLemmaNameAndIndexList :: Script -> [(String, [Int])]
scriptToConflictingLemmaNameAndIndexList [] = []
scriptToConflictingLemmaNameAndIndexList s
 | null duplicatedNames = []
 | otherwise = map (\dupName -> (dupName, map snd (filter (\(n, i) -> dupName == n) lemmaNameAndIndexList))) duplicatedNames
       where
              lemmaNameAndIndexList = scriptToLemmaNameAndIndexList s
              duplicatedNames = doubles (map fst lemmaNameAndIndexList)
