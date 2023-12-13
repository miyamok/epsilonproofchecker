import Syntax
import Proof
import Script
import Unification
import Parser
import PrettyPrint
import SMTLib
import System.Directory.Internal.Prelude (getArgs)
import System.Directory
import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace
import Data.List

printHelpMessage :: IO ()
printHelpMessage = do --putStrLn "-d option to apply deduction transformation"
                      putStrLn "-p option to print out the proof"
                      --putStrLn "-1 option to limit the application of deduction transformation only for one assumption"
                      putStrLn "Usage:"
                      putStrLn "./Main [options] filepath"

-------------------------------------------------
-- handling command line options and arguments
-------------------------------------------------

argsToDebugFlag :: [String] -> Bool
argsToDebugFlag = elem "--debug"

argsToPrintFlag :: [String] -> Bool
argsToPrintFlag = elem "-p"

argsToFilename :: [String] -> [String]
argsToFilename args = [ s | s <- args, notElem s ["--debug", "-p"] ]

argsToFlagsAndFilename :: [String] -> (Bool, Bool, [String])
argsToFlagsAndFilename args = (elem "--debug" args, elem "-p" args, argsToFilename args)

--------------------------------------------------
-- Output
--------------------------------------------------

printProofCorrect :: Proof -> Bool -> IO ()
printProofCorrect p pFlag = do putStrLn ("-- Correct proof of " ++ (prettyPrintJudgment asms f))
                               if pFlag then putStrLn (prettyPrintProof p) else return ()
                               where
                                asms = proofToAssumptionFormulas p
                                f = proofToConclusion p

printErrorMessage :: Int -> String -> IO ()
printErrorMessage ln msg = putStrLn ("-- Error at line " ++ show ln ++ ": " ++ msg)

printErrorMessageSeveralLines :: [Int] -> String -> IO ()
printErrorMessageSeveralLines lns msg = putStrLn ("-- Error at lines " ++ intercalate ", " (map show lns) ++ ": " ++ msg)

printProofWrong :: Proof -> Maybe Int -> [Int] -> IO ()
printProofWrong p mi is =
        case mi of Nothing -> do putStrLn "The input is not a proof of"
                                 putStrLn (prettyPrintFormula f)
                                 if null asms then return ()
                                              else do putStrLn "from the following assumptions"
                                                      putStrLn (prettyPrintAssumptions asms)
                   Just i -> printErrorMessage (i+1) "formula mismatching"
                where
                        f = proofToConclusion p
                        asms = proofToAssumptionFormulas p

proofBlockWithAutoToWrongLineIndex :: (Proof, [Int], Maybe String) -> Lemmas -> IO (Maybe Int)
proofBlockWithAutoToWrongLineIndex (p, lns, mn) lemmas
 | not $ and bs = do return mln
 | null autoFlas = do return Nothing
 | otherwise = do ex <- findExecutable "z3"
                  autobs <- sequence autoResults
                  case ex of Nothing -> do putStrLn "Proof by Auto requires Microsoft's Z3 (github.com/Z3Prover/z3)"
                                           case findIndex (\(_, r, _) -> r == Auto) p of
                                                Nothing -> return Nothing
                                                Just i -> return (Just (lns!!i))
                             Just _ -> if and autobs then return Nothing
                                       else let mi' = do j <- findIndex not autobs
                                                         return (lns!!(findIndices (\(_, r, _) -> r == Auto) p!!j))
                                             in case mi' of Nothing -> return Nothing; Just i' -> return (Just (lns!!i'))
 where
        bs = checkClaims p lemmas
        mi = findIndex not bs
        mln = do i <- mi
                 return (lns!!i)
        autoSteps = proofToAutoStepFormulas p
        asmFlas = proofToAssumptionFormulas p
        autoFlas = proofToAutoStepFormulas p
        autoResults = map (\autoFla -> checkFormulaByZ3 $ foldr ImpForm autoFla asmFlas) autoFlas

checkProofWithAuto :: Proof -> Lemmas -> IO Bool
checkProofWithAuto p lemmas
 | not $ and $ checkClaims p lemmas = return False
 | null autoFlas = return True
 | otherwise = do ex <- findExecutable "z3"
                  autobs <- sequence autoResults
                  case ex of Nothing -> return False
                             Just _ -> if and autobs then return True
                                       else return False
 where
        asmFlas = proofToAssumptionFormulas p
        autoFlas = proofToAutoStepFormulas p
        autoResults = map (\autoFla -> checkFormulaByZ3 $ foldr ImpForm autoFla asmFlas) autoFlas

proofBlocksAndFlagsToOutput :: [(Proof, [Int], Maybe String)] -> Bool -> Bool -> IO ()
proofBlocksAndFlagsToOutput = proofBlocksAndFlagsToOutputAux emptyLemmas

proofBlocksAndFlagsToOutputAux :: Lemmas -> [(Proof, [Int], Maybe String)] -> Bool -> Bool -> IO ()
proofBlocksAndFlagsToOutputAux _ [] _ _ = return ()
proofBlocksAndFlagsToOutputAux lemmas ((p, lns, mn):pbs) pFlag debugFlag =
        do b <- checkProofWithAuto p lemmas
           if b then do if null pbs then printProofCorrect p pFlag
                                    else let lemmas' = case mn of Nothing -> lemmas
                                                                  Just n -> Map.insert n p lemmas
                                          in proofBlocksAndFlagsToOutputAux lemmas' pbs pFlag debugFlag
                else do mi <- proofBlockWithAutoToWrongLineIndex (p, lns, mn) lemmas
                        printProofWrong p mi lns
                        if debugFlag then do putStr $ prettyPrintProof p
                                     else return ()

printConflictingDeclarationError :: Script -> IO ()
printConflictingDeclarationError s
 | not (null varDef) = printErrorMessage ((snd (head varDef))+1) "Declaration conflicts against the default constants or predicates"
 | not (null constDef) = printErrorMessage ((snd (head constDef))+1) "Declaration conflicts against the default variables or predicates"
 | not (null predDef) = printErrorMessage ((snd (head predDef))+1) "Declaration conflicts against the default variables or constants"
 | not (null confVarDecLNs) = let (ns, i) = head confVarDecLNs
                                in printErrorMessage (i+1) "Declaration conflicts against another declaration"
 | not (null confConstDecLNs) = let (ns, i) = head confConstDecLNs
                                in printErrorMessage (i+1) "Declaration conflicts against another declaration"
 | not (null confPredDecLNs) = let (ns, i) = head confPredDecLNs
                                in printErrorMessage (i+1) "Declaration conflicts against another declaration"
        where
                conflictingNames = scriptToConflictingIdentifierNames s
                varDef = scriptToConflictingVariableDeclarationsWithLNsDueToDefaultDeclarations s
                varDecLNs = scriptToVariableDeclarationsWithLineIndices s
                confVarDecLNs = filter (\(vds, i) -> not (null (vds `intersect` conflictingNames))) varDecLNs
                vnames = concat $ map fst varDecLNs
                constDef = scriptToConflictingConstantDeclarationsWithLNsDueToDefaultDeclarations s
                constDecLNs = scriptToConstantDeclarationsWithLineIndices s
                cds = concat $ map fst constDecLNs
                cnames = map fst cds
                confConstDecLNs = filter (\(cds, i) -> not (null (map fst cds `intersect` conflictingNames))) constDecLNs
                predDef = scriptToConflictingPredicateDeclarationsWithLNsDueToDefaultDeclarations s
                predDecLNs = scriptToPredicateDeclarationsWithLineIndices s
                pds = concat $ map fst predDecLNs
                pnames = map fst pds
                confPredDecLNs = filter (\(pds, i) -> not (null (map fst pds `intersect` conflictingNames))) predDecLNs

printConflictingLemmaError :: (String, [Int]) -> IO ()
printConflictingLemmaError (name, indices) = printErrorMessageSeveralLines (map (1+) indices) ("Duplicated lemma name \"" ++ name ++ "\"")

main :: IO ()
main = do args <- getArgs
          let (debugFlag, pFlag, filenames) = argsToFlagsAndFilename args
          if length filenames /= 1
          then do putStrLn "Wrong option given, otherwise not exactly one filename given"
                  printHelpMessage
          else do ls <- fmap lines (readFile (head filenames))
                  let script = parseLines ls
                      mErrorMsg = scriptToErrorMessage script
                      proofBlocks = scriptToProofBlocks script
                      conflictingIdentNames = scriptToConflictingIdentifierNames script
                      conflictingLemmas = scriptToConflictingLemmaNameAndIndexList script
                     in if not (null conflictingIdentNames)
                        then printConflictingDeclarationError script
                        else if not (null conflictingLemmas)
                        then printConflictingLemmaError (head conflictingLemmas)
                        else case mErrorMsg of
                              Just msg -> putStrLn msg
                              Nothing -> proofBlocksAndFlagsToOutput proofBlocks pFlag debugFlag
