import Syntax
import Proof
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

printProofCorrect :: Proof -> Bool -> IO()
printProofCorrect p pFlag = do putStrLn ("-- Correct proof of " ++ (prettyPrintJudgment asms f))
                               if pFlag then putStrLn (prettyPrintProof p) else return ()
                               where
                                asms = proofToAssumptionFormulas p
                                f = proofToConclusion p

printProofWrong :: Proof -> Maybe Int -> IO ()
printProofWrong p mLinenum = do case mLinenum of Nothing -> return ()
                                                 Just lineNum -> putStrLn ("Error at line " ++ show lineNum ++ ": "
                                                  ++ prettyPrintProofStep (p!!(lineNum-1)))
                                putStrLn "The input is not a proof of"
                                putStrLn (prettyPrintFormula f)
                                if null asms then return ()
                                             else do putStrLn "from the following assumptions"
                                                     putStrLn (prettyPrintAssumptions asms)
                where
                        f = proofToConclusion p
                        asms = proofToAssumptionFormulas p

proofAndFlagsToOutput :: Proof -> Maybe [Int] -> Bool -> Bool -> IO ()
proofAndFlagsToOutput p mlinenums pFlag debugFlag
 | not $ and bs = printProofWrong p mln
 | null autoFlas = printProofCorrect p pFlag
 | otherwise = do ex <- findExecutable "z3"
                  autobs <- sequence autoResults
                  case ex of Nothing -> putStrLn "Proof by Auto requires Microsoft's z3"
                             Just _ -> if and autobs then printProofCorrect p pFlag
                                       else let mi = do j <- findIndex not autobs
                                                        linenums <- mlinenums
                                                        return (linenums!!(findIndices (\(_, r, _) -> r == Auto) p!!j))
                                             in printProofWrong p mi
 where
        bs = checkClaims p
        mln = do linenums <- mlinenums
                 i <- findIndex not bs
                 return (linenums!!i)
        autoSteps = proofToAutoStepFormulas p
        asmFlas = proofToAssumptionFormulas p
        autoFlas = proofToAutoStepFormulas p
        autoResults = map (\autoFla -> checkFormulaByZ3 $ foldr ImpForm autoFla asmFlas) autoFlas

main :: IO ()
main = do args <- getArgs
          let (debugFlag, dFlag, onceFlag, pFlag, filenames) = argsToFlagsAndFilename args
          if length filenames /= 1
          then putStrLn "Wrong option given, otherwise not exactly one filename given"
          else do ls <- fmap lines (readFile (head filenames))
                  let parsedLines = parseLines ls
                      mErrorMsg = parsedLinesToErrorMessage parsedLines
                      in case mErrorMsg of
                            Just msg -> do putStrLn msg; return ()
                            Nothing -> if dFlag && not deductible
                                       then putStrLn "Deduction transformation doesn't support a proof with Auto"
                                       else proofAndFlagsToOutput proof' (if dFlag then Nothing else Just linenums) pFlag debugFlag
                              where proof = parsedLinesToProof parsedLines
                                    linenums = parsedLinesToLineNumbers parsedLines
                                    deductible = isDeductionApplicable proof
                                    proof' = if dFlag && deductible
                                             then if onceFlag then deductionOnce $ proofToUntaggedProof proof
                                                              else deduction $ proofToUntaggedProof proof
                                             else proof
