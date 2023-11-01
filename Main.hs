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
    if length args == 1
        then do ls <- fmap lines (readFile (head args))
                let p = map (\l -> fst (head (parse (line defaultPredicates defaultVariables defaultConstants) l))) ls
                    b = checkProof p
                    asms = proofToAssumptionFormulas p
                    (f, r, t) = last p
                    stmt = prettyPrintFormula f
                    fs = intercalate ", " (map prettyPrintFormula asms)
                  in if b then
                    do  putStrLn "Correct proof of"
                        putStrLn (intercalate " " [fs, "⊢", stmt])
                     else do putStrLn "Not a proof of"
                             putStrLn stmt
                             return ()
        else print "exactly one argument required for the path to your proof script."
    return ()