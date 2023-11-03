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
                putStrLn "Usage:"
                putStrLn "% ./Main [options] filepath"
        else let filename = last args
                 debugFlag = "--debug" `elem` args
                 dFlag = "-d" `elem` args
                 onceFlag = "-1" `elem` args
                 pFlag = "-p" `elem` args in
             do ls <- fmap lines (readFile filename)
                let p = map (\l -> fst (head (parse (step defaultPredicates defaultVariables defaultConstants) l))) ls
                    -- here, there should be a check, so that it fails if there is the parser did not consume all characters.
                    b = checkProof p
                    asms = proofToAssumptionFormulas p
                    (f, r, t) = last p
                    stmt = prettyPrintFormula f
                    fs = intercalate ", " (map prettyPrintFormula asms)
                  in if not b
                    then do putStrLn "The input is not a proof of"
                            putStrLn stmt
                    else if dFlag
                        then do putStrLn "The input is a correct proof of"
                                putStrLn (intercalate " " [fs, "⊢", stmt])
                                let dp = if onceFlag then deductionOnce p else deduction p in
                                    if checkProof dp
                                        then do putStrLn "It generated a correct proof of"
                                                let (f', _, _) = last dp in
                                                       do putStrLn ("⊢ " ++ prettyPrintFormula f')
                                                          if pFlag then putStrLn (prettyPrintProof dp)
                                                                   else return ()
                                        else do putStrLn "Proof transformation doesn't support this proof yet."
                                                if debugFlag then putStrLn (prettyPrintProof dp) else return ()
                    else do putStrLn "Correct proof of"
                            putStrLn (intercalate " " [fs, "⊢", stmt])
                            if pFlag then putStrLn (prettyPrintProof p) else return ()


                    --               else 

                    -- do  putStrLn "Correct proof of"
                    --     putStrLn (intercalate " " [fs, "⊢", stmt])
                    --     if dFlag then
                    --      let dp = deduction p in
                    --          do putStrLn (prettyPrintProof dp)
                    --             if checkProof dp then return () else putStrLn "deduction failed!"
                    --     else if pFlag then putStrLn (prettyPrintProof p) else return ()
                    --  else do putStrLn "Not a proof of"
                    --          putStrLn stmt
                    --          return ()

                --   in if b then
                --     do  putStrLn "Correct proof of"
                --         putStrLn (intercalate " " [fs, "⊢", stmt])
                --         if dFlag then
                --          let dp = deduction p in
                --              do putStrLn (prettyPrintProof dp)
                --                 if checkProof dp then return () else putStrLn "deduction failed!"
                --         else if pFlag then putStrLn (prettyPrintProof p) else return ()
                --      else do putStrLn "Not a proof of"
                --              putStrLn stmt
                --              return ()
                --return ()