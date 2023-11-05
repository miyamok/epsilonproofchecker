import Syntax
import Proof
import Axiom
import Parser
import System.Directory.Internal.Prelude (getArgs)
import System.Directory
import Debug.Trace
import Data.List
import PrettyPrint
import SMTLib

printHelpMessage :: IO ()
printHelpMessage = do putStrLn "-d option to apply proof transformation due to deduction theorem"
                      putStrLn "-p option to print out the proof"
                      putStrLn "-1 option to limit the application of deduction theorem only once"
                      putStrLn "Usage:"
                      putStrLn "% ./Main [options] filepath"

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

--- needed to refactor
proofAndFlagsToOutput :: Proof -> Bool -> Bool -> Bool -> Bool -> IO()
proofAndFlagsToOutput p dFlag onceFlag pFlag debugFlag =
    let b = checkProof p
        asms = proofToAssumptionFormulas p
        (f, r, t) = last p
        stmt = prettyPrintFormula f
        fs = intercalate ", " (map prettyPrintFormula asms)
        autoFlas = proofToAutoStepFormulas p
        autoResults = map (\autoFla -> checkFormulaByZ3 $ foldr ImpForm autoFla asms) autoFlas
        in if dFlag && not (null autoFlas)
        then do putStrLn "Deduction transformation doesn't support a proof with Auto"
        else if null autoFlas && b
                then if dFlag
                then do let up = proofToUntaggedProof p
                            dp = if onceFlag then deductionOnce up else deduction up in
                            if checkProof dp
                            then do putStrLn "It generated a correct proof of"
                                    let (f', _, _) = last dp in
                                        do putStrLn ("⊢ " ++ prettyPrintFormula f')
                                           if pFlag then putStrLn (prettyPrintProof dp) else return ()
                            else do putStrLn "Proof transformation doesn't support this proof yet."
                                    if debugFlag then putStrLn (prettyPrintProof dp) else return ()
                else do putStrLn "Correct proof of"
                        putStrLn (intercalate " " [fs, "⊢", stmt])
                        if pFlag then putStrLn (prettyPrintProof p) else return ()
                else do bs <- sequence autoResults
                        if and bs && b then do putStrLn "Correct proof of"
                                               putStrLn (intercalate " " [fs, "⊢", stmt])
                                               if pFlag then putStrLn (prettyPrintProof p) else return ()
                                else do putStrLn "The input is not a proof of"
                                        putStrLn stmt
                                        if null fs then return ()
                                        else do putStrLn "from the following assumptions"
                                                putStrLn fs

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
                                Nothing -> proofAndFlagsToOutput (parsedLinesToProof parsedLines) dFlag onceFlag pFlag debugFlag
