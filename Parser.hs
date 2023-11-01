module Parser where
import Control.Applicative ( Alternative(..) )
import Data.Char
import Syntax
import Proof
import Axiom

newtype Parser a = P(String -> [(a, String)])
type IdentDeclarations = ([VariableDeclaration], [ConstantDeclaration], [PredicateDeclaration])

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

-- ident :: Parser String
-- ident = do x <- lower
--            xs <- many alphanum
--            return (x:xs)

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

--identifier = token ident
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

-- negformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
-- negformula pds vds cds = do symbol "~"
--                             f <- primitiveformula pds vds cds
--                             return (NegForm f)

-- naming is wrong.  it should be improved
primitiveformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
primitiveformula pds vds cds = do symbol "("
                                  f <- impformula pds vds cds
                                  symbol ")"
                                  return f
                           <|> do symbol "~"
                                  f <- primitiveformula pds vds cds
                                  return (makeNegForm f)
                           <|> do symbol "all"
                                  x <- variable vds
                                  f <- primitiveformula pds vds cds
                                  return (ForallForm x f)
                           <|> do symbol "ex"
                                  x <- variable vds
                                  f <- primitiveformula pds vds cds
                                  return (ExistsForm x f)
                           <|> do predformula pds vds cds

-- parensformula :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Formula
-- parensformula pds vds cds = do symbol "("
--                                f <- formula pds vds cds
--                                symbol ")"
--                                return f

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

line :: [PredicateDeclaration] -> [VariableDeclaration] -> [ConstantDeclaration] -> Parser Line
line pds vds cds = do f <- formula pds vds cds
                      r <- rule
                      t <- tag
                      return (f, r, t)

defaultVariables :: [String]
defaultVariables = ["x", "y", "z", "u", "v"]

defaultConstants :: [(String, Int)]
defaultConstants = [("f",1), ("g", 1), ("c", 0), ("a", 0), ("b", 0), ("h", 2)]

defaultPredicates :: [(String, Int)]
defaultPredicates = [("P", 1), ("A", 0), ("Q", 1), ("R", 2), ("B", 0), ("C", 0)]

