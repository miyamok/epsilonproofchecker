import Syntax
import Proof
import Axiom
import Parser
import System.Directory.Internal.Prelude (getArgs)
import Debug.Trace
import Data.List
import PrettyPrint

main :: IO ()
main = do
    args <- getArgs
    if length args == 0
        then do putStrLn "at least one argument required for the path to your proof script."
                putStrLn "-d option to apply proof transformation due to deduction theorem"
                putStrLn "-p option to print out the proof"
                putStrLn "Usage:  > ./Main [-p] [-t] FILENAME"
        else let filename = last args
                 dFlag = "-d" `elem` args
                 pFlag = "-p" `elem` args in
             do ls <- fmap lines (readFile filename)
                let p = map (\l -> fst (head (parse (step defaultPredicates defaultVariables defaultConstants) l))) ls
                    -- here, there should be a check, so that it fails if there is the parser did not consume all characters.
                    b = checkProof p
                    asms = proofToAssumptionFormulas p
                    (f, r, t) = last p
                    stmt = prettyPrintFormula f
                    fs = intercalate ", " (map prettyPrintFormula asms)
                  in if b then
                    do  putStrLn "Correct proof of"
                        putStrLn (intercalate " " [fs, "⊢", stmt])
                        if dFlag then
                         let dp = deduction p in
                             do putStrLn (prettyPrintProof dp)
                                if checkProof dp then return () else putStrLn "deduction failed!"
                        else if pFlag then putStrLn (prettyPrintProof p) else return ()
                     else do putStrLn "Not a proof of"
                             putStrLn stmt
                             return ()
    return ()