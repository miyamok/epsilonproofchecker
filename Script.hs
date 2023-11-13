module Script where
import Data.List(nub, findIndex, findIndices, delete, intersect)
import Data.Maybe(listToMaybe)
import Syntax
import Proof
import Utils
import Debug.Trace

data ScriptLine = ProofLine Step | VarDeclareLine [VariableDeclaration] | ConstDeclareLine [ConstantDeclaration]
 | PredDeclareLine [PredicateDeclaration] | EmptyLine | ErrorLine String | EndProofLine (Maybe String)
 | DeductionTransformationLine (Maybe Int) (Maybe String) deriving (Show)
type Script = [ScriptLine]
type ScriptBlock = (Script, Int, Maybe String)
type ProofBlock = (Proof, [Int], Maybe String)

scriptToErrorMessage :: Script -> Maybe String
scriptToErrorMessage [] = Just "Empty input"
scriptToErrorMessage ls =
    do i <- findIndex (\l -> case l of ErrorLine s -> True; _ -> False) ls
       l <- listToMaybe [e | e@(ErrorLine _) <- ls]
       s <- case l of ErrorLine s -> Just s ; _ -> Nothing
       return ("Error at line " ++ show (i+1) ++ ": " ++ s)

scriptToProof :: Script -> Proof
scriptToProof [] = []
scriptToProof (ProofLine x:ls) = x:scriptToProof ls
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
scriptToVariableDeclarationsWithLineIndices = scriptToVariableDeclarationsWithLineIndicesAux 0

scriptToVariableDeclarationsWithLineIndicesAux :: Int -> Script -> [([VariableDeclaration], Int)]
scriptToVariableDeclarationsWithLineIndicesAux _ [] = []
scriptToVariableDeclarationsWithLineIndicesAux i (VarDeclareLine ds:ls) = (ds, i):scriptToVariableDeclarationsWithLineIndicesAux (i+1) ls
scriptToVariableDeclarationsWithLineIndicesAux i (_:ls) = scriptToVariableDeclarationsWithLineIndicesAux (i+1) ls

scriptToConstantDeclarationsWithLineIndices :: Script -> [([ConstantDeclaration], Int)]
scriptToConstantDeclarationsWithLineIndices = scriptToConstantDeclarationsWithLineIndicesAux 0

scriptToConstantDeclarationsWithLineIndicesAux :: Int -> Script -> [([ConstantDeclaration], Int)]
scriptToConstantDeclarationsWithLineIndicesAux _ [] = []
scriptToConstantDeclarationsWithLineIndicesAux i (ConstDeclareLine ds:ls) = (ds, i):scriptToConstantDeclarationsWithLineIndicesAux (i+1) ls
scriptToConstantDeclarationsWithLineIndicesAux i (_:ls) = scriptToConstantDeclarationsWithLineIndicesAux (i+1) ls

scriptToPredicateDeclarationsWithLineIndices :: Script -> [([PredicateDeclaration], Int)]
scriptToPredicateDeclarationsWithLineIndices = scriptToPredicateDeclarationsWithLineIndicesAux 0

scriptToPredicateDeclarationsWithLineIndicesAux :: Int -> Script -> [([PredicateDeclaration], Int)]
scriptToPredicateDeclarationsWithLineIndicesAux _ [] = []
scriptToPredicateDeclarationsWithLineIndicesAux i (PredDeclareLine ds:ls) = (ds, i):scriptToPredicateDeclarationsWithLineIndicesAux (i+1) ls
scriptToPredicateDeclarationsWithLineIndicesAux i (_:ls) = scriptToPredicateDeclarationsWithLineIndicesAux (i+1) ls

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
scriptToProofBlocks = scriptToProofBlocksAux 0 [] [] Nothing

scriptToProofBlocksAux :: Int -> Proof -> [Int] -> Maybe String -> Script -> [(Proof, [Int], Maybe String)]
scriptToProofBlocksAux _ [] [] _ [] = []
scriptToProofBlocksAux _ p is ms [] = [(p, is, ms)]
scriptToProofBlocksAux i p is _ (ProofLine x:s) = scriptToProofBlocksAux (i+1) (p++[x]) (is++[i]) Nothing s
scriptToProofBlocksAux i p is _ (EndProofLine mn:s) = (p, is, mn):scriptToProofBlocksAux (i+1) [] [] Nothing s
scriptToProofBlocksAux i p is _ (DeductionTransformationLine mi Nothing:s) = (p, is, Nothing):scriptToProofBlocksAux (i+1) dp is' Nothing s
    where
        p' = proofToUntaggedProof p
        dp = case mi of Nothing -> deduction p'; Just i -> iterate deductionOnce p'!!i
        is' = replicate (length dp) (-1)
scriptToProofBlocksAux i p is _ (ErrorLine x:s) = [(p, is, Nothing)]
scriptToProofBlocksAux i p is _ (_:s) = scriptToProofBlocksAux (i+1) p is Nothing s

isProofScriptLine :: ScriptLine -> Bool
isProofScriptLine (ProofLine _) = True
isProofScriptLine (EndProofLine _) = True
isProofScriptLine (DeductionTransformationLine _ _) = True
isProofScriptLine _ = False

isDeclarationScriptLine :: ScriptLine -> Bool
isDeclarationScriptLine sl =
       any (\f -> f sl) [isVariableDeclarationScriptLine, isConstantDeclarationScriptLine, isPredicateDeclarationScriptLine]

isVariableDeclarationScriptLine :: ScriptLine -> Bool
isVariableDeclarationScriptLine (VarDeclareLine _) = True
isVariableDeclarationScriptLine _ = False

isConstantDeclarationScriptLine :: ScriptLine -> Bool
isConstantDeclarationScriptLine (ConstDeclareLine _) = True
isConstantDeclarationScriptLine _ = False

isPredicateDeclarationScriptLine :: ScriptLine -> Bool
isPredicateDeclarationScriptLine (PredDeclareLine _) = True
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
scriptToLemmaNameAndIndexList = scriptToLemmaNameAndIndexListAux 0

scriptToLemmaNameAndIndexListAux :: Int -> Script -> [(String, Int)]
scriptToLemmaNameAndIndexListAux _ [] = []
scriptToLemmaNameAndIndexListAux i (EndProofLine Nothing:ls) = scriptToLemmaNameAndIndexListAux (i+1) ls
scriptToLemmaNameAndIndexListAux i (EndProofLine (Just n):ls) = (n,i):scriptToLemmaNameAndIndexListAux (i+1) ls
scriptToLemmaNameAndIndexListAux i (_:ls) = scriptToLemmaNameAndIndexListAux (i+1) ls

scriptToConflictingLemmaNameAndIndexList :: Script -> [(String, [Int])]
scriptToConflictingLemmaNameAndIndexList [] = []
scriptToConflictingLemmaNameAndIndexList s
 | null duplicatedNames = []
 | otherwise = map (\dupName -> (dupName, map snd (filter (\(n, i) -> dupName == n) lemmaNameAndIndexList))) duplicatedNames
       where
              lemmaNameAndIndexList = scriptToLemmaNameAndIndexList s
              duplicatedNames = doubles (map fst lemmaNameAndIndexList)

