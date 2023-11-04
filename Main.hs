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

main :: IO ()
main = do
    args <- getArgs
    if null args || not (all (\a -> a `elem` ["-d", "-p", "-1", "--debug"]) (init args))
        then do putStrLn "Wrong argument given"
                printHelpMessage
        else let filename = last args
                 debugFlag = "--debug" `elem` args
                 dFlag = "-d" `elem` args
                 onceFlag = "-1" `elem` args
                 pFlag = "-p" `elem` args in
             do ls <- fmap lines (readFile filename)
                let parsedList = map (parse $ step defaultPredicates defaultVariables defaultConstants) ls
                 in case elemIndex [] parsedList of
                    Just i -> do putStrLn ("parse error at line " ++ show (i+1))
                                 putStrLn (ls!!i)
                                 return ()
                    Nothing -> case findIndex parseFailed (map head parsedList) of
                        Just j -> do putStrLn ("parse error at line " ++ show (j+1))
                                     putStrLn (ls!!j)
                                     return ()
                        Nothing ->
                            let p = map (\l -> fst (head  l)) parsedList
                                -- here, there should be a check, so that it fails if there is the parser did not consume all characters.
                                b = checkProof p
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
                                        then do putStrLn "The input is a correct proof of"
                                                putStrLn (if null asms then intercalate " " ["⊢", stmt]
                                                          else intercalate " " [fs, "⊢", stmt])
                                                let up = proofToUntaggedProof p
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
