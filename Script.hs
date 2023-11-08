module Script where
import Data.List(nub)
import Syntax
import Proof

type VariableDeclaration = Name
type ConstantDeclaration = (Name, Int)
type PredicateDeclaration = (Name, Int)
type Declarations = ([VariableDeclaration], [ConstantDeclaration], [PredicateDeclaration])

data ScriptLine = ProofLine Step | VarDeclareLine [VariableDeclaration] | ConstDeclareLine [ConstantDeclaration]
 | PredDeclareLine [PredicateDeclaration] | EmptyLine | ErrorLine String | EndProofLine (Maybe String)
 | DeductionTransformationLine (Maybe Int) (Maybe String) deriving (Show)
type Script = [ScriptLine]

defaultVariables :: [VariableDeclaration]
defaultVariables = ["x", "y", "z", "u", "v"]

defaultConstants :: [ConstantDeclaration]
defaultConstants = [("f",1), ("g", 1), ("c", 0), ("a", 0), ("b", 0), ("h", 2)]

defaultPredicates :: [PredicateDeclaration]
defaultPredicates = [("P", 1), ("A", 0), ("Q", 1), ("R", 2), ("B", 0), ("C", 0)]

emptyDeclarations :: Declarations
emptyDeclarations = ([], [], [])

defaultDeclarations :: Declarations
defaultDeclarations = (defaultVariables, defaultConstants, defaultPredicates)

scriptToErrorMessage :: Script -> Maybe String
scriptToErrorMessage [] = Just "Empty input"
scriptToErrorMessage ls =
       case last ls of ErrorLine s -> Just ("Error at line " ++ show (length ls) ++ ": " ++ s)
                       _ -> if not $ or $ map (\pl -> case pl of ProofLine step -> True; _ -> False) ls
                            then Just "Input contains no proof, but only declaration"
                            else Nothing

scriptToProof :: Script -> Proof
scriptToProof [] = []
scriptToProof (ProofLine x:ls) = x:scriptToProof ls
scriptToProof (_:ls) = scriptToProof ls

scriptToDeclarations :: Script -> Declarations
scriptToDeclarations [] = (defaultVariables, defaultConstants, defaultPredicates)
scriptToDeclarations _ = undefined

scriptToVariableDeclarations :: Script -> [VariableDeclaration]
scriptToVariableDeclarations [] = defaultVariables
scriptToVariableDeclarations (VarDeclareLine ds:ls) = ds ++ scriptToVariableDeclarations ls
scriptToVariableDeclarations (_:ls) = scriptToVariableDeclarations ls

scriptToConstantDeclarations :: Script -> [ConstantDeclaration]
scriptToConstantDeclarations [] = defaultConstants
scriptToConstantDeclarations (ConstDeclareLine ds:ls) = ds ++ scriptToConstantDeclarations ls
scriptToConstantDeclarations (_:ls) = scriptToConstantDeclarations ls

scriptToPredicateDeclarations :: Script -> [PredicateDeclaration]
scriptToPredicateDeclarations [] = defaultPredicates
scriptToPredicateDeclarations (PredDeclareLine ds:ls) = ds ++ scriptToPredicateDeclarations ls
scriptToPredicateDeclarations (_:ls) = scriptToPredicateDeclarations ls

areConsistentVariableDeclarations :: [VariableDeclaration] -> Bool
areConsistentVariableDeclarations ds = length ds == length (nub ds)

areConsistentConstantDeclarations :: [ConstantDeclaration] -> Bool
areConsistentConstantDeclarations ds = let names = map fst ds
                                           arities = map snd ds
                                       in length ds == length (nub ds) && all (>= 0) arities

areConsistentPredicateDeclarations :: [PredicateDeclaration] -> Bool
areConsistentPredicateDeclarations ds = let names = map fst ds
                                            arities = map snd ds
                                        in length ds == length (nub ds) && all (>= 0) arities

-- scriptToParsedLinesBlocks :: [ParsedLine] -> [ParsedLinesBlock]
-- scriptToParsedLinesBlocks ls = scriptToParsedLinesBlocksAux ls [] 0

-- scriptToParsedLinesBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLinesBlock]
-- scriptToParsedLinesBlocksAux [] [] ln = []
-- scriptToParsedLinesBlocksAux ((VarDeclareLine ds):ls) [] ln = undefined

scriptToParsedLinesBlocks :: Script -> [(Script, Int, Maybe String)]
scriptToParsedLinesBlocks ls = scriptToParsedLinesBlocksAux ls [] 0

scriptToParsedLinesBlocksAux :: Script -> Script -> Int -> [(Script, Int, Maybe String)]
scriptToParsedLinesBlocksAux [] [] i = []
scriptToParsedLinesBlocksAux [] ls' i = [(ls', i, Nothing)]
scriptToParsedLinesBlocksAux (ProofLine x:ls) ls' i = scriptToParsedLinesBlocksAux ls (ls'++[ProofLine x]) i
scriptToParsedLinesBlocksAux (VarDeclareLine vds:ls) [] i =
       ([VarDeclareLine vds], i, Nothing):scriptToParsedLinesBlocksAux ls [] (i+1)
scriptToParsedLinesBlocksAux (VarDeclareLine vds:ls) ls' i =
       (ls', i, Nothing):([VarDeclareLine vds], i+length ls', Nothing):scriptToParsedLinesBlocksAux ls [] (i+length ls'+1)
scriptToParsedLinesBlocksAux (PredDeclareLine pds:ls) [] i =
       ([PredDeclareLine pds], i, Nothing):scriptToParsedLinesBlocksAux ls [] (i+1)
scriptToParsedLinesBlocksAux (PredDeclareLine pds:ls) ls' i =
       (ls', i, Nothing):([PredDeclareLine pds], i+length ls', Nothing):scriptToParsedLinesBlocksAux ls [] (i+length ls'+1)
scriptToParsedLinesBlocksAux (ConstDeclareLine cds:ls) [] i =
       ([ConstDeclareLine cds], i, Nothing):scriptToParsedLinesBlocksAux ls [] (i+1)
scriptToParsedLinesBlocksAux (ConstDeclareLine cds:ls) ls' i =
       (ls', i, Nothing):([ConstDeclareLine cds], i+length ls', Nothing):scriptToParsedLinesBlocksAux ls [] (i+length ls'+1)
scriptToParsedLinesBlocksAux (EndProofLine mn:ls) ls' i =
       (ls', i, mn):scriptToParsedLinesBlocksAux ls [] (i+length ls'+1)
scriptToParsedLinesBlocksAux (DeductionTransformationLine mi mstr:ls) ls' i =
       scriptToParsedLinesBlocksAux ls (ls'++[DeductionTransformationLine mi mstr]) i
scriptToParsedLinesBlocksAux (EmptyLine:ls) ls' i = scriptToParsedLinesBlocksAux ls ls' (i+1)
scriptToParsedLinesBlocksAux (ErrorLine str:ls) ls' i = ([ErrorLine str], i, Nothing):scriptToParsedLinesBlocksAux ls ls' (i+1)

isCorrectlyStructuredBlocks :: [(Script, Int, Maybe String)] -> Bool
isCorrectlyStructuredBlocks = isCorrectlyStructuredBlocksAux False

isCorrectlyStructuredBlocksAux :: Bool -> [(Script, Int, Maybe String)] -> Bool
isCorrectlyStructuredBlocksAux _ [] = True
isCorrectlyStructuredBlocksAux True (([VarDeclareLine _], _, _):ls) = False
isCorrectlyStructuredBlocksAux False (([VarDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
isCorrectlyStructuredBlocksAux True (([ConstDeclareLine _], _, _):ls) = False
isCorrectlyStructuredBlocksAux False (([ConstDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
isCorrectlyStructuredBlocksAux True (([PredDeclareLine _], _, _):ls) = False
isCorrectlyStructuredBlocksAux False (([PredDeclareLine _], _, _):ls) = isCorrectlyStructuredBlocksAux False ls
isCorrectlyStructuredBlocksAux isMainMatter (([EmptyLine], _, _):ls) = isCorrectlyStructuredBlocksAux isMainMatter ls
isCorrectlyStructuredBlocksAux isMainMatter (([ErrorLine _], _, _):ls) = isCorrectlyStructuredBlocksAux isMainMatter ls
isCorrectlyStructuredBlocksAux _ (([ProofLine _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
isCorrectlyStructuredBlocksAux _ (([EndProofLine _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
isCorrectlyStructuredBlocksAux _ (([DeductionTransformationLine _ _], _, _):ls) = isCorrectlyStructuredBlocksAux True ls
isCorrectlyStructuredBlocksAux _ _ = True

scriptBlocksToIllegalDeclarationIndex :: [(Script, Int, Maybe String)] -> Maybe Int
scriptBlocksToIllegalDeclarationIndex = scriptBlocksToIllegalDeclarationIndexAux False

scriptBlocksToIllegalDeclarationIndexAux :: Bool -> [(Script, Int, Maybe String)] -> Maybe Int
scriptBlocksToIllegalDeclarationIndexAux _ [] = Nothing
scriptBlocksToIllegalDeclarationIndexAux True (([VarDeclareLine _], i, _):ls) = Just i
scriptBlocksToIllegalDeclarationIndexAux False (([VarDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
scriptBlocksToIllegalDeclarationIndexAux True (([ConstDeclareLine _], i, _):ls) = Just i
scriptBlocksToIllegalDeclarationIndexAux False (([ConstDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
scriptBlocksToIllegalDeclarationIndexAux True (([PredDeclareLine _], i, _):ls) = Just i
scriptBlocksToIllegalDeclarationIndexAux False (([PredDeclareLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux False ls
scriptBlocksToIllegalDeclarationIndexAux isMainMatter (([EmptyLine], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux isMainMatter ls
scriptBlocksToIllegalDeclarationIndexAux isMainMatter (([ErrorLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux isMainMatter ls
scriptBlocksToIllegalDeclarationIndexAux _ (([ProofLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
scriptBlocksToIllegalDeclarationIndexAux _ (([EndProofLine _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
scriptBlocksToIllegalDeclarationIndexAux _ (([DeductionTransformationLine _ _], _, _):ls) = scriptBlocksToIllegalDeclarationIndexAux True ls
scriptBlocksToIllegalDeclarationIndexAux _ _ = Nothing

-- scriptToProofBlocks :: [ParsedLine] -> [ProofBlock]
-- scriptToProofBlocks [] = []
-- scriptToProofBlocks (ProofLine x:ls) = x:scriptToProofBlocks ls
-- scriptToProofBlocks (_:ls) = scriptToProofBlocks ls

-- scriptToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLine]
-- scriptToProofBlocksAux [] [] offset = []
-- scriptToProofBlocksAux [] stack offset = stack
-- scriptToProofBlocksAux (ProofLine x:ls) stack offset = (stack++[ProofLine x]):scriptToProofBlocksAux ls [] offset
-- scriptToProofBlocksAux (EndProofLine mn:ls) stack offset = []

-- scriptToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ProofBlock]
-- scriptToProofBlocksAux [] [] offset = []
-- scriptToProofBlocksAux [] stack offset = [(Nothing, scriptToProof stack, offset)]
-- scriptToProofBlocksAux (l:ls) [] offset = []

scriptToLineNumbers :: Script -> [Int]
scriptToLineNumbers ls = scriptToLineNumbersAux ls 1

scriptToLineNumbersAux :: Script -> Int -> [Int]
scriptToLineNumbersAux [] ln = []
scriptToLineNumbersAux (ProofLine x:ls) ln = ln:scriptToLineNumbersAux ls (ln+1)
scriptToLineNumbersAux (_:ls) ln = scriptToLineNumbersAux ls (ln+1)
