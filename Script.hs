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
 where varDecsLNs = scriptToVariableDeclarationsWithLineNumbers s
       varDecs = concat $ map fst varDecsLNs
       constDecsLNs = scriptToConstantDeclarationsWithLineNumbers s
       constDecs = concat $ map fst constDecsLNs
       predDecsLNs = scriptToPredicateDeclarationsWithLineNumbers s
       predDecs = concat $ map fst predDecsLNs

scriptToVariableDeclarationsWithLineNumbers :: Script -> [([VariableDeclaration], Int)]
scriptToVariableDeclarationsWithLineNumbers = scriptToVariableDeclarationsWithLineNumbersAux 0

scriptToVariableDeclarationsWithLineNumbersAux :: Int -> Script -> [([VariableDeclaration], Int)]
scriptToVariableDeclarationsWithLineNumbersAux _ [] = []
scriptToVariableDeclarationsWithLineNumbersAux i (VarDeclareLine ds:ls) = (ds, i):scriptToVariableDeclarationsWithLineNumbersAux (i+1) ls
scriptToVariableDeclarationsWithLineNumbersAux i (_:ls) = scriptToVariableDeclarationsWithLineNumbersAux (i+1) ls

scriptToConstantDeclarationsWithLineNumbers :: Script -> [([ConstantDeclaration], Int)]
scriptToConstantDeclarationsWithLineNumbers = scriptToConstantDeclarationsWithLineNumbersAux 0

scriptToConstantDeclarationsWithLineNumbersAux :: Int -> Script -> [([ConstantDeclaration], Int)]
scriptToConstantDeclarationsWithLineNumbersAux _ [] = []
scriptToConstantDeclarationsWithLineNumbersAux i (ConstDeclareLine ds:ls) = (ds, i):scriptToConstantDeclarationsWithLineNumbersAux (i+1) ls
scriptToConstantDeclarationsWithLineNumbersAux i (_:ls) = scriptToConstantDeclarationsWithLineNumbersAux (i+1) ls

scriptToPredicateDeclarationsWithLineNumbers :: Script -> [([PredicateDeclaration], Int)]
scriptToPredicateDeclarationsWithLineNumbers = scriptToPredicateDeclarationsWithLineNumbersAux 0

scriptToPredicateDeclarationsWithLineNumbersAux :: Int -> Script -> [([PredicateDeclaration], Int)]
scriptToPredicateDeclarationsWithLineNumbersAux _ [] = []
scriptToPredicateDeclarationsWithLineNumbersAux i (PredDeclareLine ds:ls) = (ds, i):scriptToPredicateDeclarationsWithLineNumbersAux (i+1) ls
scriptToPredicateDeclarationsWithLineNumbersAux i (_:ls) = scriptToPredicateDeclarationsWithLineNumbersAux (i+1) ls

-- scriptToInconsistentVariableDeclarationsWithLineNumbersDueToDefaultNames :: Script -> [(Name, Int)]
-- scriptToInconsistentVariableDeclarationsWithLineNumbersDueToDefaultNames s
--  | null varDecs = undefined
--  | null constDecs && meets vars defaultConstantNames = undefined
--  where varDecs = scriptToVariableDeclarationsWithLineNumbers s
--        constDecs = scriptToConstantDeclarationsWithLineNumbers s
--        predDecs = scriptToPredicateDeclarationsWithLineNumbers s

scriptToInconsistentIdentifierNames :: Script -> [Name]
scriptToInconsistentIdentifierNames s = declarationsToInconsistentIdentifierNames (scriptToDeclarations s)

--scriptAndConflictingIdentifierNameToErrorMessage :: Script -> Name -> String

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
                                            (scriptToVariableDeclarationsWithLineNumbers s)
              -- constDecLNs = scriptToConstantDeclarationsWithLineNumbers s
              -- predDecLNs = scriptToPredicateDeclarationsWithLineNumbers s

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
                                              (scriptToConstantDeclarationsWithLineNumbers s)
              -- constDecLNs = scriptToConstantDeclarationsWithLineNumbers s
              -- predDecLNs = scriptToPredicateDeclarationsWithLineNumbers s

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
                                              (scriptToPredicateDeclarationsWithLineNumbers s)

-- scriptToInconsistentDeclarationIndices :: Script -> [Int]
-- scriptToInconsistentDeclarationIndices s = undefined

-- scriptToInconsistentIdentifierNames :: Script -> [String]
-- scriptToInconsistentIdentifierNames s
-- -- cases conflicting against defaults
--  | null varDecs && meets consts defaultVariables = let wrong = filter (\(decs, i) -> meets defaultVariables (map fst decs)) constDecs
--                                                         in undefined
--  | null varDecs && meets preds defaultVariables = undefined
--  | null constDecs && meets vars defaultConstantNames = undefined
--  | null constDecs && meets preds defaultConstantNames = undefined
--  | null predDecs && meets vars defaultPredicateNames = undefined
--  | null predDecs && meets consts defaultPredicateNames = undefined
-- -- otherwise conflicting among explicit declarations (no concern of defaults)
--  | otherwise = undefined
--  where varDecs = scriptToVariableDeclarationsWithLineNumbers s
--        constDecs = scriptToConstantDeclarationsWithLineNumbers s
--        predDecs = scriptToPredicateDeclarationsWithLineNumbers s
--        vars = if null varDecs then defaultVariables else concat $ map fst varDecs
--        consts = map fst $ if null constDecs then defaultConstants else concat $ map fst constDecs
--        preds = map fst $ if null predDecs then defaultPredicates else concat $ map fst predDecs
--        doubledNames = doubles (vars ++ consts ++ preds)
--        probVarDecs = filter (\(decs, ln) -> meets doubledNames decs) varDecs
--        probConstDecs = filter (\(decs, ln) -> meets doubledNames (map fst decs)) constDecs
--        probPredDecs = filter (\(decs, ln) -> meets doubledNames (map fst decs)) predDecs
--        defaultConstantNames = map fst defaultConstants
--        defaultPredicateNames = map fst defaultPredicates

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

-- scriptToFirstProofAndLineNumbers :: Script -> (Proof, [Int])
-- scriptToFirstProofAndLineNumbers [] = ([], [])
-- scriptToFirstProofAndLineNumbers (ProofLine x:ls) = undefined

-- scriptToProofScripts :: Script -> [Script]
-- scriptToProofScripts = scriptToProofScriptsAux []

-- scriptToProofScriptsAux :: Script -> Script -> [Script]
-- scriptToProofScriptsAux [] (ProofLine x:ls) = scriptToProofScriptsAux [ProofLine x] ls
-- scriptToProofScriptsAux s (ProofLine x:ls) = scriptToProofScriptsAux (s++[ProofLine x]) ls
-- scriptToProofScriptsAux [] (EndProofLine mn:ls) = [EndProofLine mn]:scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux s (EndProofLine mn:ls) = (s++[EndProofLine mn]):scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux [] (DeductionTransformationLine mi ml:ls) = [DeductionTransformationLine mi ml]:scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux s (DeductionTransformationLine mi ml:ls) = s:scriptToProofScriptsAux [DeductionTransformationLine mi ml] ls
-- scriptToProofScriptsAux [] (VarDeclareLine _:ls) = [EmptyLine]:scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux s (VarDeclareLine _:ls) = scriptToProofScriptsAux (s++[EmptyLine]) ls
-- scriptToProofScriptsAux [] (ConstDeclareLine _:ls) = [EmptyLine]:scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux s (ConstDeclareLine _:ls) = scriptToProofScriptsAux (s++[EmptyLine]) ls
-- scriptToProofScriptsAux [] (PredDeclareLine _:ls) = [EmptyLine]:scriptToProofScriptsAux [] ls
-- scriptToProofScriptsAux s (PredDeclareLine _:ls) = scriptToProofScriptsAux (s++[EmptyLine]) ls
-- scriptToProofScriptsAux s (ErrorLine x:ls) = s:[ErrorLine x]:scriptToProofScriptsAux [] ls

-- -- proof script contains either ProofLine, EndProofLine, DeductionTransformation, EmptyLine, or ErrorLine

-- proofScriptsToProofBlocks :: [Script] -> [(Proof, [Maybe Int], Maybe String)]
-- proofScriptsToProofBlocks = proofScriptsToProofBlocksAux 0 [] []

-- -- to define a type of proofscript
-- proofScriptsToProofBlocksAux :: Int -> Proof -> [Maybe Int] -> [Script] -> [(Proof, [Maybe Int], Maybe String)]
-- proofScriptsToProofBlocksAux _ p lineNums [] = [(p, lineNums, Nothing)]
-- proofScriptsToProofBlocksAux i p lineNums ((ProofLine x:s):ss) = proofScriptsToProofBlocksAux (i+1) (p++[x]) (lineNums ++ [Just i]) s
-- proofScriptsToProofBlocksAux i p lineNums (EndProofLine mn:s) = (p, lineNums, mn):proofScriptsToProofBlocksAux (i+1) [] [] s
-- proofScriptsToProofBlocksAux i p lineNums (DeductionTransformationLine mi mn:s) = (p, lineNums, Nothing):proofScriptsToProofBlocksAux (i+1) genProof nothings s
--     where genProof = case mi of Nothing -> deduction p
--                                 Just i -> iterate deductionOnce p !! i
--           nothings = replicate (length genProof) Nothing
-- proofScriptsToProofBlocksAux i p lineNums (EmptyLine:s) = proofScriptsToProofBlocksAux (i+1) p lineNums s
-- proofScriptsToProofBlocksAux i p lineNums (ErrorLine x:s) = (p, lineNums, Nothing):proofScriptsToProofBlocksAux (i+1) [] [] s





-- scriptToScriptWithOffsetListAux _ s i [] = [(s, i)]
-- scriptToScriptWithOffsetListAux offset s i (ProofLine x:ls) = scriptToScriptWithOffsetListAux (offset + 1) (s++[ProofLine x]) i ls
-- scriptToScriptWithOffsetListAux offset s i (VarDeclareLine _:ls) = scriptToScriptWithOffsetListAux (offset + 1) (s++[EmptyLine]) i ls
-- scriptToScriptWithOffsetListAux offset s i (ConstDeclareLine _:ls) = scriptToScriptWithOffsetListAux (offset + 1) (s++[EmptyLine]) i ls
-- scriptToScriptWithOffsetListAux offset s i (PredDeclareLine _:ls) = scriptToScriptWithOffsetListAux (offset + 1) (s++[EmptyLine]) i ls
-- scriptToScriptWithOffsetListAux offset s i (EndProofLine x:ls) = (s, i):scriptToScriptWithOffsetListAux (offset + 1) [] i ls

-- scriptToProofAndLineNumbersList :: Script -> [(Proof, [Int] ,Maybe String)]
-- scriptToProofAndLineNumbersList = scriptToProofAndLineNumbersListAux 0 [] []

-- scriptToProofAndLineNumbersListAux :: Int -> Proof -> [Int] -> Script -> [(Proof, [Int], Maybe String)]
-- scriptToProofAndLineNumbersListAux _ p lineNums [] = [(p, lineNums, Nothing)]
-- scriptToProofAndLineNumbersListAux i p lineNums (ProofLine x:ls) = scriptToProofAndLineNumbersListAux (i+1) (p++[x]) (lineNums++[i]) ls
-- scriptToProofAndLineNumbersListAux i p lineNums (DeductionTransformationLine mi Nothing:ls) =
--     [(p, lineNums, Nothing), (deduction p, [], Nothing)] ++ scriptToProofAndLineNumbersListAux (i+1) (p++[x]) (lineNums++[i]) ls

-- scriptToScriptBlocks :: [ParsedLine] -> [ParsedLinesBlock]
-- scriptToParsedLinesBlocks ls = scriptToParsedLinesBlocksAux ls [] 0

-- scriptToParsedLinesBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLinesBlock]
-- scriptToParsedLinesBlocksAux [] [] ln = []
-- scriptToParsedLinesBlocksAux ((VarDeclareLine ds):ls) [] ln = undefined

-- scriptToParagraphs :: Script -> [Paragraph]
-- scriptToParagraphs ls = scriptToParagraphsAux ls ([], 0, Nothing) 0

-- scriptToParagraphsAux :: Script -> Script -> Int -> [Paragraph]
-- -- scriptToParagraphsAux scriptToProcess  offset
-- scriptToParagraphsAux [] [] _ = []
-- scriptToParagraphsAux [] ls i = [(ls, i, Nothing)]
-- scriptToParagraphsAux [VarDeclareLine x:ls] ls' _ = undefined

-- scriptToScriptBlocks :: Script -> [(Script, Maybe Int)]
-- scriptToScriptBlocks = scriptToScriptBlocksAux [] (Just 0)

-- scriptToScriptBlocksAux :: Script -> Maybe Int -> Script -> [(Script, Maybe Int)]
-- scriptToScriptBlocksAux [] _ [] = []
-- scriptToScriptBlocksAux ls' mi [] = [(ls', mi)]
-- scriptToScriptBlocksAux ls' mi (ProofLine x:ls) = scriptToScriptBlocksAux (ls'++[ProofLine x]) mi ls
-- scriptToScriptBlocksAux ls' mi (EndProofLine mn:ls) =
--        (ls'++[EndProofLine mn], mi):scriptToScriptBlocksAux [] (fmap (length ls'+1+) mi) ls
-- scriptToScriptBlocksAux ls' mi' (DeductionTransformationLine mi mstr:ls) =
--        scriptToScriptBlocksAux (ls'++[DeductionTransformationLine mi mstr]) mi' ls
-- scriptToScriptBlocksAux ls' mi (EmptyLine:ls) = scriptToScriptBlocksAux (ls'++[EmptyLine]) mi ls
-- scriptToScriptBlocksAux ls' mi (ErrorLine str:ls) =
--        ([ErrorLine str], mi):scriptToScriptBlocksAux ls' (fmap (1+) mi) ls
-- scriptToScriptBlocksAux [] mi (VarDeclareLine vds:ls) =
--        ([VarDeclareLine vds], mi):scriptToScriptBlocksAux [] (mi >>= \i -> Just (i+1)) ls
-- scriptToScriptBlocksAux ls' mi (VarDeclareLine vds:ls) =
--        (ls', mi):([VarDeclareLine vds], fmap (length ls'+) mi):scriptToScriptBlocksAux [] (fmap (length ls'+1+) mi) ls
-- scriptToScriptBlocksAux [] mi (PredDeclareLine pds:ls) =
--        ([PredDeclareLine pds], mi):scriptToScriptBlocksAux [] (fmap (1+) mi) ls
-- scriptToScriptBlocksAux ls' mi (PredDeclareLine pds:ls) =
--        (ls', mi):([PredDeclareLine pds], fmap (length ls'+) mi):scriptToScriptBlocksAux [] (fmap (length ls'+1+) mi) ls
-- scriptToScriptBlocksAux [] mi (ConstDeclareLine cds:ls) =
--        ([ConstDeclareLine cds], mi):scriptToScriptBlocksAux [] (fmap (1+) mi) ls
-- scriptToScriptBlocksAux ls' mi (ConstDeclareLine cds:ls) =
--        (ls', mi):([ConstDeclareLine cds], fmap (length ls'+) mi):scriptToScriptBlocksAux [] (fmap (length ls'+1+) mi) ls

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

-- scriptBlockToLineNumbers :: (Script, Maybe Int, Maybe String) -> [Maybe Int]
-- --scriptBlockToLineNumbers (s, Nothing, _) = replicate (length s) Nothing
-- scriptBlockToLineNumbers ([], _, _) = []
-- scriptBlockToLineNumbers ((ProofLine x):ls, mi, _) = undefined

-- isCorrectlyStructuredBlocks :: [(Script, Int, Maybe String)] -> Bool
-- isCorrectlyStructuredBlocks = isCorrectlyStructuredBlocksAux False

-- isCorrectlyStructuredBlocksAux :: Bool -> [(Script, Int, Maybe String)] -> Bool
-- isCorrectlyStructuredBlocksAux _ [] = True
-- isCorrectlyStructuredBlocksAux True (([VarDeclareLine _], _, _):ls) = False
-- isCorrectlyStructuredBlocksAux False (([VarDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
-- isCorrectlyStructuredBlocksAux True (([ConstDeclareLine _], _, _):ls) = False
-- isCorrectlyStructuredBlocksAux False (([ConstDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
-- isCorrectlyStructuredBlocksAux True (([PredDeclareLine _], _, _):ls) = False
-- isCorrectlyStructuredBlocksAux False (([PredDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
-- isCorrectlyStructuredBlocksAux isMainMatter (([EmptyLine], _, _):ls) = isCorrectlyStructuredBlocksAux isMainMatter ls
-- isCorrectlyStructuredBlocksAux isMainMatter (([ErrorLine _], _, _):ls) = isCorrectlyStructuredBlocksAux isMainMatter ls
-- isCorrectlyStructuredBlocksAux _ (([ProofLine _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
-- isCorrectlyStructuredBlocksAux _ (([EndProofLine _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
-- isCorrectlyStructuredBlocksAux _ (([DeductionTransformationLine _ _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
-- isCorrectlyStructuredBlocksAux _ _ = True

-- scriptBlocksToIllegalDeclarationIndex :: [(Script, Int, Maybe String)] -> Maybe Int
-- scriptBlocksToIllegalDeclarationIndex = scriptBlocksToIllegalDeclarationIndexAux False

-- scriptBlocksToIllegalDeclarationIndexAux :: Bool -> [(Script, Int, Maybe String)] -> Maybe Int
-- scriptBlocksToIllegalDeclarationIndexAux _ [] = Nothing
-- scriptBlocksToIllegalDeclarationIndexAux True (([VarDeclareLine _], i, _):ls) = Just i
-- scriptBlocksToIllegalDeclarationIndexAux False (([VarDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
-- scriptBlocksToIllegalDeclarationIndexAux True (([ConstDeclareLine _], i, _):ls) = Just i
-- scriptBlocksToIllegalDeclarationIndexAux False (([ConstDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
-- scriptBlocksToIllegalDeclarationIndexAux True (([PredDeclareLine _], i, _):ls) = Just i
-- scriptBlocksToIllegalDeclarationIndexAux False (([PredDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
-- scriptBlocksToIllegalDeclarationIndexAux isMainMatter (([EmptyLine], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux isMainMatter ls
-- scriptBlocksToIllegalDeclarationIndexAux isMainMatter (([ErrorLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux isMainMatter ls
-- scriptBlocksToIllegalDeclarationIndexAux _ (([ProofLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
-- scriptBlocksToIllegalDeclarationIndexAux _ (([EndProofLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
-- scriptBlocksToIllegalDeclarationIndexAux _ (([DeductionTransformationLine _ _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
-- scriptBlocksToIllegalDeclarationIndexAux _ _ = Nothing

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

-- scriptToInconsistentDeclarationsIndices :: Script -> [Int]
-- scriptToInconsistentDeclarationsIndices s = do fpi <- findIndex isProofScriptLine s
--                                                let dis = findIndices isDeclarationScriptLine s



-- scriptToProofBlocks :: Script -> [(Proof, [Int], Maybe String)]
-- scriptToProofBlocks = scriptToProofBlocksAux 0 []

-- scriptToProofBlocksAux :: Int -> Script -> Script -> [(Proof, [Int], Maybe String)]
-- -- scriptToProofBlocksAux i curr orig = 
-- scriptToProofBlocksAux i curr [] = undefined
-- scriptToProofBlocks :: [ParsedLine] -> [ProofBlock]
-- scriptToProofBlocks [] = []
-- scriptToProofBlocks (ProofLine x:ls) = x:scriptToProofBlocks ls
-- scriptToProofBlocks (_:ls) = scriptToProofBlocks ls

-- scriptToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLine]
-- scriptToProofBlocksAux [] [] offset = []
-- scriptToProofBlocksAux [] stack offset = stack
-- scriptToProofBlocksAux (ProofLine x:ls) stack offset = (stack++[ProofLine x]):scriptToProofBlocksAux ls [] offset
-- scriptToProofBlocksAux (EndProofLine mn:ls) stack offset = []

-- scriptToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ProofBlock]
-- scriptToProofBlocksAux [] [] offset = []
-- scriptToProofBlocksAux [] stack offset = [(Nothing, scriptToProof stack, offset)]
-- scriptToProofBlocksAux (l:ls) [] offset = []

-- scriptToLineNumbers :: Script -> [Int]
-- scriptToLineNumbers ls = scriptToLineNumbersAux ls 1

-- scriptToLineNumbersAux :: Script -> Int -> [Int]
-- scriptToLineNumbersAux [] ln = []
-- scriptToLineNumbersAux (ProofLine x:ls) ln = ln:scriptToLineNumbersAux ls (ln+1)
-- scriptToLineNumbersAux (DeductionTransformationLine mi mn:ls) ln = ln:scriptToLineNumbersAux ls (ln+1)
-- scriptToLineNumbersAux (_:ls) ln = scriptToLineNumbersAux ls (ln+1)
