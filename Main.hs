import Syntax
import Proof
import Axiom
import Parser
import System.Directory.Internal.Prelude (getArgs)
import Debug.Trace

main :: IO ()
main = do
    args <- getArgs
    if length args == 1
        then do ls <- fmap lines (readFile (head args))
                let p = map (\l -> fst (head (parse (line defaultPredicates defaultVariables defaultConstants) l))) ls
                    b = checkProof p
                    (f, r, t) = last p
                    stmt = formulaToString f
                  in if b then
                     do putStrLn stmt
                        putStrLn "is proved"
                        return ()
                     else do putStrLn "Not a proof of"
                             putStrLn stmt
                             return ()
        else print "exactly one argument for the path to your proof script."
    return ()