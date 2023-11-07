module Parser where
import Control.Applicative ( Alternative(..) )
import Data.Char
import Syntax
import Proof
import Axiom

newtype Parser a = P(String -> [(a, String)])
data ParsedLine = ProofLine Step | VarDeclareLine [VariableDeclaration] | ConstDeclareLine [ConstantDeclaration]
 | PredDeclareLine [PredicateDeclaration] | EmptyLine | ErrorLine String | EndProofLine (Maybe String)
 | DeductionTransformationLine (Maybe Int) (Maybe String) deriving (Show)
--type ParsedLinesBlock = ([ParsedLine], Int, Maybe String)
--data ParsedLinesBlock = ProofBlock [(ParsedLine, Int)] (Maybe String) | DeclarationBlock [(ParsedLine, Int)]
parse :: Parser a -> String -> [(a, String)]
parse (P p) inp = p inp

item :: Parser Char
item = P (\inp -> case inp of
    [] -> []
    (x:xs) -> [(x,xs)])

instance Functor Parser where
    -- fmap :: (a -> b) -> Parser a -> Parser b
    fmap g p = P (\inp -> case parse p inp of
        [] -> []
        [(v, out)] -> [(g v, out)])

instance Applicative Parser where
    -- pure :: a -> Parser a
    pure v = P (\inp -> [(v, inp)])
    -- <*> :: Parser (a -> b) -> Parser a -> Parser b
    pg <*> px = P (\inp -> case parse pg inp of
        [] -> []
        [(g, out)] -> parse (fmap g px) out)

instance Monad Parser where
    -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
    p >>= f = P (\inp -> case parse p inp of
        [] -> []
        [(x, inp')] -> parse (f x) inp')

instance Alternative Parser where
    -- empty :: Parser a
    empty = P (\inp -> [])
    -- (<|>) :: Parser a -> Parser a -> Parser a
    p <|> q = P (\inp -> case parse p inp of
        [] -> parse q inp
        [(v, out)] -> [(v, out)])

------------------------------------
-- parser for formulas and terms
------------------------------------

sat :: (Char -> Bool) -> Parser Char
sat f = do x <- item
           if f x then return x else empty

digit :: Parser Char
digit = sat isDigit

lower :: Parser Char
lower = sat isLower

upper = sat isUpper

alphanum = sat isAlphaNum
letter = sat isLetter

string :: String -> Parser String
string [] = return []
string (x:xs) = do char x
                   string xs
                   return (x:xs)

char x = sat (== x)

nat :: Parser Int
nat = do xs <- some digit
         return (read xs)

space :: Parser ()
space = do many (char ' ')
           return ()

int :: Parser Int
int = do char '-'
         n <- nat
         return (-n)
      <|> nat

token :: Parser a -> Parser a
token p = do space
             v <- p
             space
             return v

natural = token nat
integer = token int

symbol :: String -> Parser String
symbol xs = token (string xs)

var :: [VariableDeclaration] -> Parser Variable
var [] = empty
var (vn:vns) = do n <- string vn
                  i <- integer
                  return (Var n i)
           <|> do n <- string vn
                  return (Var n (-1))
           <|> var vns

variable :: [VariableDeclaration] -> Parser Variable
variable vds = token (var vds)

constant :: [ConstantDeclaration] -> Parser Constant
constant [] = empty
constant ((n, a):ds) = do name <- string n
                          index <- integer
                          return (Syntax.Const name index a)
                   <|> do name <- string n
                          return (Syntax.Const n (-1) a)
                   <|> constant ds

constterm :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Term
constterm pds vds cds = do c <- constant cds
                           if constToArity c == 0
                            then return (AppTerm c [])
                            else do ts <- argterms pds vds cds
                                    if length ts == constToArity c
                                        then return (AppTerm c ts)
                                        else empty

epsterm :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Term
epsterm pds vds cds = do string "eps"
                         space
                         v <- variable vds
                         space
                         f <- formula pds vds cds
                         return (EpsTerm v f)

term :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Term
term [] _ _ = empty
term _ [] _ = empty
term _ _ [] = empty
term pds vds cds = do v <- variable vds
                      return (VarTerm v)
               <|> do constterm pds vds cds
               <|> do epsterm pds vds cds

argterms :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser [Term]
argterms pds vds cds = do symbol "("
                          t <- term pds vds cds
                          ts <- many (do symbol ","
                                         term pds vds cds)
                          symbol ")"
                          return (t:ts)

predconst :: [PredicateDeclaration] -> Parser Predicate
predconst [] = empty
predconst ((n, a):pds) = do name <- string n
                            index <- integer
                            return (Pred name index a)
                     <|> do name <- string n
                            return (Pred name (-1) a)
                     <|> do name <- string "bot"
                            return Falsum
                     <|> predconst pds

formula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
formula = impformula

predformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
predformula pds vds cds =
    do p <- predconst pds
       if predToArity p == 0
        then return (PredForm p [])
        else do ts <- argterms pds vds cds
                if length ts == predToArity p
                    then return (PredForm p ts)
                    else empty

impformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
impformula pds vds cds = do f <- disjformula pds vds cds
                            do symbol "->"
                               f' <- impformula pds vds cds
                               return (ImpForm f f')
                             <|> return f

disjformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
disjformula pds vds cds = do f1 <- conjformula pds vds cds
                             do symbol "|"
                                f2 <- disjformula pds vds cds
                                return (DisjForm f1 f2)
                              <|> return f1

conjformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
conjformula pds vds cds = do f1 <- primitiveformula pds vds cds
                             do symbol "&"
                                f2 <- conjformula pds vds cds
                                return (ConjForm f1 f2)
                              <|> return f1

-- naming is wrong.  it should be improved
primitiveformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
primitiveformula pds vds cds = do symbol "("
                                  f <- impformula pds vds cds
                                  symbol ")"
                                  return f
                           <|> do symbol "~"
                                  f <- primitiveformula pds vds cds
                                  return (makeNegFormula f)
                           <|> do symbol "all"
                                  x <- variable vds
                                  f <- primitiveformula pds vds cds
                                  return (ForallForm x f)
                           <|> do symbol "ex"
                                  x <- variable vds
                                  f <- primitiveformula pds vds cds
                                  return (ExistsForm x f)
                           <|> do predformula pds vds cds

------------------------------------
-- parser for proof scripts
------------------------------------

tag :: Parser (Maybe String)
tag = do symbol "#"
         t <- some alphanum
         return (Just t)
       <|> return Nothing

rule :: Parser Rule
rule = do symbol "by"
          r <- ruleAux
          return r

ruleAux :: Parser Rule
ruleAux = do symbol "K"
             return K
       <|> do symbol "S"
              return S
       <|> do symbol "ConjE1"
              return ConjE1
       <|> do symbol "ConjE2"
              return ConjE2
       <|> do symbol "ConjI"
              return ConjI
       <|> do symbol "DisjI1"
              return DisjI1
       <|> do symbol "DisjI2"
              return DisjI2
       <|> do symbol "DisjE"
              return DisjE
       <|> do symbol "EFQ"
              return EFQ
       <|> do symbol "DNE"
              return DNE
       <|> do symbol "AllE"
              return AllE
       <|> do symbol "ExI"
              return ExI
       <|> do symbol "AllShift"
              return AllShift
       <|> do symbol "ExShift"
              return ExShift
       <|> do symbol "Gen"
              symbol "("
              arg <- tag
              symbol ")"
              return (Gen arg)
       <|> do symbol "Gen"
              return (Gen Nothing)
       <|> do symbol "C"
              return C
       <|> do symbol "MP"
              symbol "("
              arg1 <- tag
              symbol ","
              arg2 <- tag
              symbol ")"
              return (MP arg1 arg2)
       <|> do symbol "MP"
              return (MP Nothing Nothing)
       <|> do symbol "Asm"
              return Asm
       <|> do symbol "Auto"
              return Auto

step :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Step
step pds vds cds = do f <- formula pds vds cds
                      r <- rule
                      t <- tag
                      return (f, r, t)

defaultVariables :: [String]
defaultVariables = ["x", "y", "z", "u", "v"]

defaultConstants :: [(String, Int)]
defaultConstants = [("f",1), ("g", 1), ("c", 0), ("a", 0), ("b", 0), ("h", 2)]

defaultPredicates :: [(String, Int)]
defaultPredicates = [("P", 1), ("A", 0), ("Q", 1), ("R", 2), ("B", 0), ("C", 0)]

pt :: String -> Term
pt s = let res = parse (term defaultPredicates defaultVariables defaultConstants) s
       in case res of [(t, r)] -> t

pf :: String -> Formula
pf s = let res = parse (formula defaultPredicates defaultVariables defaultConstants) s
       in case res of [(f, r)] -> f

parseFailed :: (a, String) -> Bool
parseFailed (_, "") = False
parseFailed (_, _) = True

-------------------------------
-- declarations
-------------------------------

variableDeclaration :: Parser [String]
variableDeclaration = do kind <- string "variables "
                         do name <- some letter
                            names <- many (do string " "
                                              some letter)
                            return (name:names)


constantDeclaration :: Parser [(String, Int)]
constantDeclaration = do arity <- nat
                         kind <- string "ary-constants "
                         do name <- some letter
                            names <- many (do string " "
                                              some letter)
                            return [(n, arity) | n <- name:names]

predicateDeclaration :: Parser [(String, Int)]
predicateDeclaration = do arity <- nat
                          kind <- string "ary-predicates "
                          do name <- some letter
                             names <- many (do string " "
                                               some letter)
                             return [(n, arity) | n <- name:names]

--------------------------------
-- comment line and empty line
--------------------------------

commentLine :: Parser ()
commentLine = do string "--"
                 many (sat (\c -> True))
                 return ()

emptyLine :: Parser ()
emptyLine = do many (string " ")
               return ()

endProofLine :: Parser ParsedLine
endProofLine = do symbol "end-proof"
                  name <- many alphanum
                  if null name then return (EndProofLine Nothing)
                               else return (EndProofLine (Just name))

deductionTransformationLine :: Parser ParsedLine
deductionTransformationLine = do symbol "deduction-transformation"
                                 name <- many alphanum
                                 if null name then return (DeductionTransformationLine Nothing Nothing)
                                 else return (DeductionTransformationLine Nothing (Just name))
                            <|> do symbol "bounded-deduction-transformation"
                                   i <- nat
                                   space
                                   name <- many alphanum
                                   if null name then return (DeductionTransformationLine (Just i) Nothing)
                                   else return (DeductionTransformationLine (Just i) (Just name))

proofScriptLine :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser ParsedLine
proofScriptLine pds vds cds =
           do vd <- variableDeclaration
              return (VarDeclareLine vd)
       <|> do cd <- constantDeclaration
              return (ConstDeclareLine cd)
       <|> do pd <- predicateDeclaration
              return (PredDeclareLine pd)
       <|> do step <- step pds vds cds
              return (ProofLine step)
       <|> do mn <- endProofLine
              return mn
       <|> do mn <- deductionTransformationLine
              return mn
       <|> do commentLine
              return EmptyLine
       <|> do emptyLine
              return EmptyLine

parseLines :: [String] -> [ParsedLine]
parseLines ls = parseLinesAux ls [] [] []

parseLinesAux :: [String] -> [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> [ParsedLine]
parseLinesAux [] pds vds cds = []
parseLinesAux (l:ls) pds vds cds =
       let mpl = parse (proofScriptLine (if null pds then defaultPredicates else pds)
                                        (if null vds then defaultVariables else vds)
                                        (if null cds then defaultConstants else cds)) l
           aux = parseLinesAux ls
        in case mpl of [] -> [ErrorLine l]
                       [(pl, str)] ->
                            if null str
                            then case pl of (ProofLine step) -> ProofLine step:aux pds vds cds
                                            (VarDeclareLine newds) -> VarDeclareLine newds:aux pds (vds++newds) cds
                                            (PredDeclareLine newds) -> PredDeclareLine newds:aux (pds++newds) vds cds
                                            (ConstDeclareLine newds) -> ConstDeclareLine newds:aux pds vds (cds++newds)
                                            EndProofLine ms -> EndProofLine ms:aux pds vds cds
                                            DeductionTransformationLine mi ms ->
                                                 DeductionTransformationLine mi ms:aux pds vds cds
                                            EmptyLine -> EmptyLine:aux pds vds cds
                            else [ErrorLine l]
                       _ -> [ErrorLine l]

parsedLinesToErrorMessage :: [ParsedLine] -> Maybe String
parsedLinesToErrorMessage [] = Just "Empty input"
parsedLinesToErrorMessage ls =
       case last ls of ErrorLine s -> Just ("Error at line " ++ show (length ls) ++ ": " ++ s)
                       _ -> if not $ or $ map (\pl -> case pl of ProofLine step -> True; _ -> False) ls
                            then Just "Input contains no proof, but only declaration"
                            else Nothing

parsedLinesToProof :: [ParsedLine] -> Proof
parsedLinesToProof [] = []
parsedLinesToProof (ProofLine x:ls) = x:parsedLinesToProof ls
parsedLinesToProof (_:ls) = parsedLinesToProof ls

-- parsedLinesToParsedLinesBlocks :: [ParsedLine] -> [ParsedLinesBlock]
-- parsedLinesToParsedLinesBlocks ls = parsedLinesToParsedLinesBlocksAux ls [] 0

-- parsedLinesToParsedLinesBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLinesBlock]
-- parsedLinesToParsedLinesBlocksAux [] [] ln = []
-- parsedLinesToParsedLinesBlocksAux ((VarDeclareLine ds):ls) [] ln = undefined

parsedLinesToParsedLinesBlocks :: [ParsedLine] -> [([ParsedLine], Int, Maybe String)]
parsedLinesToParsedLinesBlocks ls = parsedLinesToParsedLinesBlocksAux ls [] 0

parsedLinesToParsedLinesBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [([ParsedLine], Int, Maybe String)]
parsedLinesToParsedLinesBlocksAux [] [] i = []
parsedLinesToParsedLinesBlocksAux [] ls' i = [(ls', i, Nothing)]
parsedLinesToParsedLinesBlocksAux (ProofLine x:ls) ls' i = parsedLinesToParsedLinesBlocksAux ls (ls'++[ProofLine x]) i
parsedLinesToParsedLinesBlocksAux (VarDeclareLine vds:ls) [] i =
       ([VarDeclareLine vds], i, Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+1)
parsedLinesToParsedLinesBlocksAux (VarDeclareLine vds:ls) ls' i =
       (ls', i, Nothing):([VarDeclareLine vds], i+length ls', Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+length ls'+1)
parsedLinesToParsedLinesBlocksAux (PredDeclareLine pds:ls) [] i =
       ([PredDeclareLine pds], i, Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+1)
parsedLinesToParsedLinesBlocksAux (PredDeclareLine pds:ls) ls' i =
       (ls', i, Nothing):([PredDeclareLine pds], i+length ls', Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+length ls'+1)
parsedLinesToParsedLinesBlocksAux (ConstDeclareLine cds:ls) [] i =
       ([ConstDeclareLine cds], i, Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+1)
parsedLinesToParsedLinesBlocksAux (ConstDeclareLine cds:ls) ls' i =
       (ls', i, Nothing):([ConstDeclareLine cds], i+length ls', Nothing):parsedLinesToParsedLinesBlocksAux ls [] (i+length ls'+1)
parsedLinesToParsedLinesBlocksAux (EndProofLine mn:ls) ls' i =
       (ls', i, mn):parsedLinesToParsedLinesBlocksAux ls [] (i+length ls'+1)
parsedLinesToParsedLinesBlocksAux (DeductionTransformationLine mi mstr:ls) ls' i =
       parsedLinesToParsedLinesBlocksAux ls (ls'++[DeductionTransformationLine mi mstr]) i
parsedLinesToParsedLinesBlocksAux (EmptyLine:ls) ls' i = parsedLinesToParsedLinesBlocksAux ls ls' (i+1)
parsedLinesToParsedLinesBlocksAux (ErrorLine str:ls) ls' i = ([ErrorLine str], i, Nothing):parsedLinesToParsedLinesBlocksAux ls ls' (i+1)

isCorrectlyStructuredBlocks :: [([ParsedLine], Int, Maybe String)] -> Bool
isCorrectlyStructuredBlocks = isCorrectlyStructuredBlocksAux False

isCorrectlyStructuredBlocksAux :: Bool -> [([ParsedLine], Int, Maybe String)] -> Bool
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

parsedLinesBlocksToIllegalDeclarationIndex :: [([ParsedLine], Int, Maybe String)] -> Maybe Int
parsedLinesBlocksToIllegalDeclarationIndex = parsedLinesBlocksToIllegalDeclarationIndexAux False

parsedLinesBlocksToIllegalDeclarationIndexAux :: Bool -> [([ParsedLine], Int, Maybe String)] -> Maybe Int
parsedLinesBlocksToIllegalDeclarationIndexAux _ [] = Nothing
parsedLinesBlocksToIllegalDeclarationIndexAux True (([VarDeclareLine _], i, _):ls) = Just i
parsedLinesBlocksToIllegalDeclarationIndexAux False (([VarDeclareLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux False ls
parsedLinesBlocksToIllegalDeclarationIndexAux True (([ConstDeclareLine _], i, _):ls) = Just i
parsedLinesBlocksToIllegalDeclarationIndexAux False (([ConstDeclareLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux False ls
parsedLinesBlocksToIllegalDeclarationIndexAux True (([PredDeclareLine _], i, _):ls) = Just i
parsedLinesBlocksToIllegalDeclarationIndexAux False (([PredDeclareLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux False ls
parsedLinesBlocksToIllegalDeclarationIndexAux isMainMatter (([EmptyLine], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux isMainMatter ls
parsedLinesBlocksToIllegalDeclarationIndexAux isMainMatter (([ErrorLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux isMainMatter ls
parsedLinesBlocksToIllegalDeclarationIndexAux _ (([ProofLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux True ls
parsedLinesBlocksToIllegalDeclarationIndexAux _ (([EndProofLine _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux True ls
parsedLinesBlocksToIllegalDeclarationIndexAux _ (([DeductionTransformationLine _ _], _, _):ls) = parsedLinesBlocksToIllegalDeclarationIndexAux True ls
parsedLinesBlocksToIllegalDeclarationIndexAux _ _ = Nothing

-- parsedLinesToProofBlocks :: [ParsedLine] -> [ProofBlock]
-- parsedLinesToProofBlocks [] = []
-- parsedLinesToProofBlocks (ProofLine x:ls) = x:parsedLinesToProofBlocks ls
-- parsedLinesToProofBlocks (_:ls) = parsedLinesToProofBlocks ls

-- parsedLinesToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ParsedLine]
-- parsedLinesToProofBlocksAux [] [] offset = []
-- parsedLinesToProofBlocksAux [] stack offset = stack
-- parsedLinesToProofBlocksAux (ProofLine x:ls) stack offset = (stack++[ProofLine x]):parsedLinesToProofBlocksAux ls [] offset
-- parsedLinesToProofBlocksAux (EndProofLine mn:ls) stack offset = []

-- parsedLinesToProofBlocksAux :: [ParsedLine] -> [ParsedLine] -> Int -> [ProofBlock]
-- parsedLinesToProofBlocksAux [] [] offset = []
-- parsedLinesToProofBlocksAux [] stack offset = [(Nothing, parsedLinesToProof stack, offset)]
-- parsedLinesToProofBlocksAux (l:ls) [] offset = []

parsedLinesToLineNumbers :: [ParsedLine] -> [Int]
parsedLinesToLineNumbers ls = parsedLinesToLineNumbersAux ls 1

parsedLinesToLineNumbersAux :: [ParsedLine] -> Int -> [Int]
parsedLinesToLineNumbersAux [] ln = []
parsedLinesToLineNumbersAux (ProofLine x:ls) ln = ln:parsedLinesToLineNumbersAux ls (ln+1)
parsedLinesToLineNumbersAux (_:ls) ln = parsedLinesToLineNumbersAux ls (ln+1)

------------------------------------
-- parser for command line options
------------------------------------

-- debugFlag :: Parser Bool
-- debugFlag = do symbol "--debug"
--                return True

-- deductionFlag :: Parser Bool
-- deductionFlag = do symbol "-d"
--                    return True

-- onceFlag :: Parser Bool
-- onceFlag = do symbol "-1"
--               return True

-- printFlag :: Parser Bool
-- printFlag = do symbol "-p"
--                return True

-- argsToDebugFlag :: [String] -> Bool
-- argsToDebugFlag args = or $ map (\b -> if null b then False else let [(_, s)]=b in null s) (map (parse debugFlag) args)

-- argsToDeductionFlag :: [String] -> Bool
-- argsToDeductionFlag args = or $ map (\b -> if null b then False else let [(_, s)]=b in null s) (map (parse deductionFlag) args)

-- argsToOnceFlag :: [String] -> Bool
-- argsToOnceFlag args = or $ map (\b -> if null b then False else let [(_, s)]=b in null s) (map (parse onceFlag) args)

-- argsToPrintFlag :: [String] -> Bool
-- argsToPrintFlag args = or $ map (\b -> if null b then False else let [(_, s)]=b in null s) (map (parse printFlag) args)
