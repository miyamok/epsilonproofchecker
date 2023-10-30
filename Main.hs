import Syntax
import Proof
import Axiom
import Parser
import System.Directory.Internal.Prelude (getArgs)

main :: IO ()
main = do
    args <- getArgs
    if length args == 1
        then do ls <- fmap lines (readFile (args !! 0))
                print (checkProof (map (\l -> fst((parse (line defaultPredicates defaultVariables defaultConstants) l)!!0)) ls))
        else print "exactly one argument for the path to your proof script."
    return ()