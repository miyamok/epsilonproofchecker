module Parser where
import Control.Applicative ( Alternative(..) )
import Data.Char
import Data.List
import Syntax
import Proof
import Script
import Axiom

newtype Parser a = P(String -> [(a, String)])

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

upper :: Parser Char
upper = sat isUpper

alphanum :: Parser Char
alphanum = sat isAlphaNum

letter :: Parser Char
letter = sat isLetter

string :: String -> Parser String
string [] = return []
string (x:xs) = do char x
                   string xs
                   return (x:xs)

char :: Char -> Parser Char
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

natural :: Parser Int
natural = token nat

integer :: Parser Int
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

appterm :: Declarations -> Parser Term
appterm (vds, cds, pds) = do c <- constant cds
                             if constToArity c == 0
                             then return (AppTerm c [])
                             else do ts <- argterms (vds, cds, pds)
                                     if length ts == constToArity c
                                     then return (AppTerm c ts)
                                     else empty

epsterm :: Declarations -> Parser Term
epsterm (vds, cds, pds) = do string "eps"
                             space
                             v <- variable vds
                             space
                             f <- formula (vds, cds, pds)
                             return (EpsTerm v f)

term :: Declarations -> Parser Term
term (vds, cds, pds) = do v <- variable vds
                          return (VarTerm v)
                   <|> do appterm (vds, cds, pds)
                   <|> do epsterm (vds, cds, pds)

argterms :: Declarations -> Parser [Term]
argterms (vds, cds, pds) = do symbol "("
                              t <- term (vds, cds, pds)
                              ts <- many (do symbol ","
                                             term (vds, cds, pds))
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

formula :: Declarations -> Parser Formula
formula = impformula

predformula :: Declarations -> Parser Formula
predformula (vds, cds, pds) =
    do p <- predconst pds
       if predToArity p == 0
        then return (PredForm p [])
        else do ts <- argterms (vds, cds, pds)
                if length ts == predToArity p
                    then return (PredForm p ts)
                    else empty

impformula :: Declarations -> Parser Formula
impformula (vds, cds, pds) = do f <- disjformula (vds, cds, pds)
                                do symbol "->"
                                   f' <- impformula (vds, cds, pds)
                                   return (ImpForm f f')
                                 <|> return f

disjformula :: Declarations -> Parser Formula
disjformula (vds, cds, pds) = do f1 <- conjformula (vds, cds, pds)
                                 do symbol "|"
                                    f2 <- disjformula (vds, cds, pds)
                                    return (DisjForm f1 f2)
                                  <|> return f1

conjformula :: Declarations -> Parser Formula
conjformula (vds, cds, pds) = do f1 <- primitiveformula (vds, cds, pds)
                                 do symbol "&"
                                    f2 <- conjformula (vds, cds, pds)
                                    return (ConjForm f1 f2)
                                  <|> return f1

-- naming is wrong.  it should be improved
primitiveformula :: Declarations -> Parser Formula
primitiveformula (vds, cds, pds) = do symbol "("
                                      f <- impformula (vds, cds, pds)
                                      symbol ")"
                                      return f
                               <|> do symbol "~"
                                      f <- primitiveformula (vds, cds, pds)
                                      return (makeNegFormula f)
                               <|> do symbol "all"
                                      x <- variable vds
                                      f <- primitiveformula (vds, cds, pds)
                                      return (ForallForm x f)
                               <|> do symbol "ex"
                                      x <- variable vds
                                      f <- primitiveformula (vds, cds, pds)
                                      return (ExistsForm x f)
                               <|> do predformula (vds, cds, pds)

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

step :: Declarations -> Parser Step
step (vds, cds, pds) = do f <- formula (vds, cds, pds)
                          r <- rule
                          t <- tag
                          return (f, r, t)

pt :: String -> Term
pt s = let res = parse (term defaultDeclarations) s
       in case res of [(t, r)] -> t

pf :: String -> Formula
pf s = let res = parse (formula defaultDeclarations) s
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

endProofLine :: Parser ScriptLine
endProofLine = do symbol "end-proof"
                  name <- many alphanum
                  if null name then return (EndProofLine Nothing)
                               else return (EndProofLine (Just name))

deductionTransformationLine :: Parser ScriptLine
deductionTransformationLine = do symbol "deduction-transformation-repeatedly"
                                 name <- many alphanum
                                 if null name then return (DeductionTransformationLine Nothing Nothing)
                                 else return (DeductionTransformationLine Nothing (Just name))
                            <|> do symbol "deduction-transformation"
                                   name <- many alphanum
                                   if null name then return (DeductionTransformationLine (Just 1) Nothing)
                                   else return (DeductionTransformationLine (Just 1) (Just name))

proofScriptLine :: Declarations -> Parser ScriptLine
proofScriptLine (vds, cds, pds) =
           do vd <- variableDeclaration
              return (VarDeclareLine vd)
       <|> do cd <- constantDeclaration
              return (ConstDeclareLine cd)
       <|> do pd <- predicateDeclaration
              return (PredDeclareLine pd)
       <|> do step <- step (vds, cds, pds)
              return (ProofLine step)
       <|> do mn <- endProofLine
              return mn
       <|> do mn <- deductionTransformationLine
              return mn
       <|> do commentLine
              return EmptyLine
       <|> do emptyLine
              return EmptyLine

parseLines :: [String] -> Script
parseLines ls = parseLinesAux ls emptyDeclarations

parseLinesAux :: [String] -> Declarations -> Script
parseLinesAux [] (vds, cds, pds) = []
parseLinesAux (l:ls) (vds, cds, pds) =
       let mpl = parse (proofScriptLine (if null vds then defaultVariables else vds,
                                         if null cds then defaultConstants else cds,
                                         if null pds then defaultPredicates else pds)) l
           aux = parseLinesAux ls
        in case mpl of [] -> [ErrorLine l]
                       [(pl, str)] ->
                            if null str
                            then case pl of (ProofLine step) -> ProofLine step:aux (vds, cds, pds)
                                            (VarDeclareLine newds) -> VarDeclareLine newds:aux (vds++newds, cds, pds)
                                            (PredDeclareLine newds) -> PredDeclareLine newds:aux (vds, cds, pds++newds)
                                            (ConstDeclareLine newds) -> ConstDeclareLine newds:aux (vds, cds++newds, pds)
                                            EndProofLine ms -> EndProofLine ms:aux (vds, cds, pds)
                                            DeductionTransformationLine mi ms ->
                                                 DeductionTransformationLine mi ms:aux (vds, cds, pds)
                                            EmptyLine -> EmptyLine:aux (vds, cds, pds)
                            else [ErrorLine l]
                       _ -> [ErrorLine l]
