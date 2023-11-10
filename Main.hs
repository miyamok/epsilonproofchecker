import Syntax
import Proof
import Script
import Axiom
import Parser
import PrettyPrint
import SMTLib
import System.Directory.Internal.Prelude (getArgs)
import System.Directory
import Debug.Trace
import Data.List

printHelpMessage :: IO ()
printHelpMessage = do putStrLn "-d option to apply proof transformation due to deduction theorem"
                      putStrLn "-p option to print out the proof"
                      putStrLn "-1 option to limit the application of deduction theorem only once"
                      putStrLn "Usage:"
                      putStrLn "% ./Main [options] filepath"

-------------------------------------------------
-- handling command line options and arguments
-------------------------------------------------

argsToDebugFlag :: [String] -> Bool
argsToDebugFlag = elem "--debug"

argsToDeductionFlag :: [String] -> Bool
argsToDeductionFlag = elem "-d"

argsToOnceFlag :: [String] -> Bool
argsToOnceFlag = elem "-1"

argsToPrintFlag :: [String] -> Bool
argsToPrintFlag = elem "-p"

argsToFilename :: [String] -> [String]
argsToFilename args = [ s | s <- args, notElem s ["--debug", "-1", "-d", "-p"] ]

argsToFlagsAndFilename :: [String] -> (Bool, Bool, Bool, Bool, [String])
argsToFlagsAndFilename args = (elem "--debug" args, elem "-d" args, elem "-1" args, elem "-p" args, argsToFilename args)

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
printErrorMessage ln msg = putStrLn ("Error at line " ++ show ln ++ ": " ++ msg)

printProofWrong :: Proof -> Maybe Int -> [Int] -> IO ()
printProofWrong p mi is =
        case mi of Nothing -> do putStrLn "The input is not a proof of"
                                 putStrLn (prettyPrintFormula f)
                                 if null asms then return ()
                                              else do putStrLn "from the following assumptions"
                                                      putStrLn (prettyPrintAssumptions asms)
                   Just i -> printErrorMessage (i+1) (prettyPrintProofStep (p!!i))
                where
                        f = proofToConclusion p
                        asms = proofToAssumptionFormulas p

printIllStructuredProofBlockError :: [(Script, Int, Maybe String)] -> IO ()
printIllStructuredProofBlockError pbs = undefined

proofAndFlagsToOutput :: Proof -> [Int] -> Bool -> Bool -> IO Bool
proofAndFlagsToOutput p is pFlag debugFlag
 | not $ and bs = do printProofWrong p mi is
                     return False
 | null autoFlas = do printProofCorrect p pFlag
                      return True
 | otherwise = do ex <- findExecutable "z3"
                  autobs <- sequence autoResults
                  case ex of Nothing -> do putStrLn "Proof by Auto requires Microsoft's z3"
                                           return False
                             Just _ -> if and autobs then do printProofCorrect p pFlag
                                                             return True
                                       else let mi' = do j <- findIndex not autobs
                                                         return (is!!(findIndices (\(_, r, _) -> r == Auto) p!!j))
                                             in do printProofWrong p mi' is
                                                   return False
 where
        bs = checkClaims p
        mi = findIndex not bs
        mln = do i <- mi
                 return (is!!i)
        autoSteps = proofToAutoStepFormulas p
        asmFlas = proofToAssumptionFormulas p
        autoFlas = proofToAutoStepFormulas p
        autoResults = map (\autoFla -> checkFormulaByZ3 $ foldr ImpForm autoFla asmFlas) autoFlas

proofBlocksAndFlagsToOutput :: [(Proof, [Int], Maybe String)] -> Bool -> Bool -> IO ()
proofBlocksAndFlagsToOutput [] _ _ = return ()
proofBlocksAndFlagsToOutput ((p, lns, ms):pbs) pFlag debugFlag =
        do b <- proofAndFlagsToOutput p lns pFlag debugFlag
           if b then proofBlocksAndFlagsToOutput pbs pFlag debugFlag
                else return ()

-- This function is needed only for a deprecated feature of the "-d" command line option
proofBlocksAndFlagsToDeductionOutput :: [(Proof, [Int], Maybe String)] -> Bool -> Bool -> Bool -> IO ()
proofBlocksAndFlagsToDeductionOutput [(proof, ln, ms)] onceFlag pFlag debugFlag
 | isDeductionApplicable proof = let proof' = if onceFlag then deductionOnce $ proofToUntaggedProof proof
                                                          else deduction $ proofToUntaggedProof proof
                                     in do b <- proofAndFlagsToOutput proof' ln pFlag debugFlag
                                           return ()
 | otherwise = putStrLn "Deduction transformation doesn't support a proof with Auto"
proofBlocksAndFlagsToDeductionOutput _ _ _ _
        = putStrLn "-d option may not be specified for a proof script with deduction-transformation or end-proof"

main :: IO ()
main = do args <- getArgs
          let (debugFlag, dFlag, onceFlag, pFlag, filenames) = argsToFlagsAndFilename args
          if length filenames /= 1
          then putStrLn "Wrong option given, otherwise not exactly one filename given"
          else do ls <- fmap lines (readFile (head filenames))
                  let script = parseLines ls
                      mErrorMsg = scriptToErrorMessage script
                      declarations = scriptToDeclarations script
                      mIllDeclInd = scriptToIllegalDeclarationIndex script
                      scriptBlocks = scriptToScriptBlocks script
                      proofBlocks = scriptToProofBlocks script
                      in case mErrorMsg of
                              Just msg -> putStrLn msg
                              Nothing -> if dFlag
                                         then proofBlocksAndFlagsToDeductionOutput proofBlocks onceFlag pFlag debugFlag
                                         else case mIllDeclInd of
                                                Nothing -> proofBlocksAndFlagsToOutput proofBlocks pFlag debugFlag
                                                Just i -> printErrorMessage (i+1) "Declaration may not occur after a proof started."
