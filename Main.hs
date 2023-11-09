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

printProofWrong :: Proof -> Maybe Int -> [Int] -> IO ()
printProofWrong p mi is =
        case mi of Nothing -> do putStrLn "The input is not a proof of"
                                 putStrLn (prettyPrintFormula f)
                                 if null asms then return ()
                                              else do putStrLn "from the following assumptions"
                                                      putStrLn (prettyPrintAssumptions asms)
                   Just i -> if i < length is && i < length p -- temporarily a line number of the erroneous proof step may be missing
                             then putStrLn ("Error at line " ++ show (is!!i+1) ++ ": " ++ prettyPrintProofStep (p!!i))
                             else putStrLn "Error found (possibly some lines after deduction-transformation??)"
                where
                        f = proofToConclusion p
                        asms = proofToAssumptionFormulas p

printIllStructuredProofBlockError :: [(Script, Int, Maybe String)] -> IO ()
printIllStructuredProofBlockError pbs = undefined

proofAndFlagsToOutput :: Proof -> [Int] -> Bool -> Bool -> IO ()
proofAndFlagsToOutput p is pFlag debugFlag
 | not $ and bs = printProofWrong p mi is
 | null autoFlas = printProofCorrect p pFlag
 | otherwise = do ex <- findExecutable "z3"
                  autobs <- sequence autoResults
                  case ex of Nothing -> putStrLn "Proof by Auto requires Microsoft's z3"
                             Just _ -> if and autobs then printProofCorrect p pFlag
                                       else let mi' = do j <- findIndex not autobs
                                                         return (is!!(findIndices (\(_, r, _) -> r == Auto) p!!j))
                                             in printProofWrong p mi' is
 where
        bs = checkClaims p
        mi = findIndex not bs
        mln = do i <- mi -- temporarily the line number of the erroneous proof step may be missing
                 if i < length is then return (is!!i) else Nothing
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
                  let script = parseLines ls
                      mErrorMsg = scriptToErrorMessage script
                      declarations = scriptToDeclarations script
                      mIllDeclInd = scriptToIllegalDeclarationIndex script
                      --proof = scriptToProof script
                      scriptBlocks = scriptToScriptBlocks script
                      proofBlocks = scriptToProofBlocks script
                      (proof, is, _) = last proofBlocks
                      --proof = scriptToProof $ concat (map (\(l, _, _) -> l) scriptBlocks)
                      --proofScripts = scriptToProofScripts script
                      --proofBlocks = proofScriptToProofBlocks proofScripts
                      --proofs = proofBlocksToProofs proofBlocks
                      --proof = proofs!!0
                      --linenums = scriptToLineNumbers script
                      deductible = isDeductionApplicable proof
                      proof' = if dFlag && deductible
                               then if onceFlag then deductionOnce $ proofToUntaggedProof proof
                                                else deduction $ proofToUntaggedProof proof
                               else proof
                --       in case scriptBlocksToIllegalDeclarationIndex scriptBlocks of
                --          Just i -> do putStrLn ("Error at line " ++ show (i+1))
                --                       putStrLn "Declarations may appear only before a proof starts"
                --          Nothing -> 
                      in case mErrorMsg of
                              Just msg -> do putStrLn msg; return ()
                              Nothing -> if dFlag && not deductible
                                         then putStrLn "Deduction transformation doesn't support a proof with Auto"
                                         else case mIllDeclInd of Nothing -> proofAndFlagsToOutput proof' is pFlag debugFlag
                                                                  Just i -> putStrLn ("Error at line " ++ show (i+1) ++ ": Declaration may not occur after a proof started.")
