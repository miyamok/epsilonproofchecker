module Syntax where
import Data.List(nub, delete, union, unionBy, intercalate)
import Data.Binary (encode)

type Name = String
type Index = Int
type Arity = Int

data Variable = Var Name Index deriving (Eq, Show, Ord)
data Constant = Const Name Index Arity deriving (Eq, Show)
data Term = VarTerm Variable | AppTerm Constant [Term] | EpsTerm Variable Formula deriving (Eq, Show)
data Predicate = Falsum | Equality | Pred Name Index Arity deriving (Eq, Show)
data Formula = PredForm Predicate [Term] | ForallForm Variable Formula | ExistsForm Variable Formula |
               ImpForm Formula Formula | ConjForm Formula Formula  | DisjForm Formula Formula
               deriving (Eq, Show)

type VariableDeclaration = Name
type ConstantDeclaration = (Name, Int)
type PredicateDeclaration = (Name, Int)

variableToIndex :: Variable -> Index
variableToIndex (Var n i) = i

variableToName :: Variable -> Name
variableToName (Var n i) = n

constToArity :: Constant -> Arity
constToArity (Const n i a) = a

predToArity :: Predicate -> Arity
predToArity (Pred n i a) = a
predToArity Falsum = 0
predToArity Equality = 2

makeVar :: Name -> Variable
makeVar n = Var n (-1)

isVariable :: Variable -> Bool
isVariable (Var n i) = not (null n) && i >= -1

isConstant :: Constant -> Bool
isConstant (Const n i a) = not (null n) && i >= -1 && a >= 0

isTerm :: Term -> Bool
isTerm (VarTerm v) = isVariable v
isTerm (AppTerm (Const n i a) ts) = isConstant (Const n i a) && (a == length ts) && all isTerm ts
isTerm (EpsTerm v f) = isFormula f

isEpsTerm :: Term -> Bool
isEpsTerm (EpsTerm v f) = isVariable v && isFormula f
isEpsTerm _ = False

epsTermToKernel :: Term -> Maybe Formula
epsTermToKernel (EpsTerm v f) = Just f
epsTermToKernel _ = Nothing

termToFreeVariables :: Term -> [Variable]
termToFreeVariables (VarTerm v) = [v]
termToFreeVariables (AppTerm c ts) = nub (concatMap termToFreeVariables ts)
termToFreeVariables (EpsTerm v f) = delete v (formulaToFreeVariables f)

termToVariables :: Term -> [Variable]
termToVariables (VarTerm v) = [v]
termToVariables (AppTerm c ts) = nub (concatMap termToVariables ts)
termToVariables (EpsTerm v f) = nub (v:formulaToVariables f)

formulaToFreeVariables :: Formula -> [Variable]
formulaToFreeVariables (PredForm p ts) = nub (concatMap termToFreeVariables ts)
formulaToFreeVariables (ForallForm v f) = delete v (formulaToFreeVariables f)
formulaToFreeVariables (ExistsForm v f) = delete v (formulaToFreeVariables f)
formulaToFreeVariables (ImpForm f1 f2) = formulaToFreeVariables f1 `union` formulaToFreeVariables f2
formulaToFreeVariables (ConjForm f1 f2) = formulaToFreeVariables f1 `union` formulaToFreeVariables f2
formulaToFreeVariables (DisjForm f1 f2) = formulaToFreeVariables f1 `union` formulaToFreeVariables f2

formulaToVariables :: Formula -> [Variable]
formulaToVariables (PredForm p ts) = nub (concatMap termToVariables ts)
formulaToVariables (ForallForm v f) = nub (v:formulaToVariables f)
formulaToVariables (ExistsForm v f) = nub (v:formulaToVariables f)
formulaToVariables (ImpForm f1 f2) = formulaToVariables f1 `union` formulaToVariables f2
formulaToVariables (ConjForm f1 f2) = formulaToVariables f1 `union` formulaToVariables f2
formulaToVariables (DisjForm f1 f2) = formulaToVariables f1 `union` formulaToVariables f2

variablesToFreshVariable :: [Variable] -> Variable
variablesToFreshVariable [] = Var "x" 0
variablesToFreshVariable (v:vs) = Var (variableToName v) (maximum (map variableToIndex (v:vs)) + 1)

isPredicate :: Predicate -> Bool
isPredicate (Pred n i a) = not (null n) && i >= -1 && a >= 0
isPredicate Falsum = True
isPredicate Equality = True

makePred :: Name -> Arity -> Predicate
makePred n a = Pred n (-1) a

formulaToConstants :: Formula -> [Constant]
formulaToConstants (PredForm p ts) = nub $ concat $ map termToConstants ts
formulaToConstants (ImpForm f g) = formulaToConstants f `union` formulaToConstants g
formulaToConstants (ConjForm f g) = formulaToConstants f `union` formulaToConstants g
formulaToConstants (DisjForm f g) = formulaToConstants f `union` formulaToConstants g
formulaToConstants (ForallForm v f) = formulaToConstants f
formulaToConstants (ExistsForm v f) = formulaToConstants f

termToConstants :: Term -> [Constant]
termToConstants (VarTerm _) = []
termToConstants (AppTerm c ts) = c:concat (map termToConstants ts)
termToCOnstants (EpsTerm v f) = formulaToConstants f


makeNegForm :: Formula -> Formula
makeNegForm f = ImpForm f falsity

isNegForm :: Formula -> Bool
isNegForm (ImpForm _ (PredForm Falsum [])) = True
isNegForm _ = False

isFormula :: Formula -> Bool
isFormula (PredForm p ts) = isPredicate p && predToArity p == length ts && all isTerm ts
isFormula (ForallForm v f) = isFormula f
isFormula (ExistsForm v f) = isFormula f
isFormula (ImpForm f1 f2) = isFormula f1 && isFormula f2
isFormula (ConjForm f1 f2) = isFormula f1 && isFormula f2
isFormula (DisjForm f1 f2) = isFormula f1 && isFormula f2

substTerm :: Variable -> Term -> Term -> Term
substTerm v t (VarTerm v2) = if v==v2 then t else VarTerm v2
substTerm v t (AppTerm c ts) = AppTerm c (map (substTerm v t) ts)
substTerm v t (EpsTerm v2 f) = if v==v2 then EpsTerm v2 f else EpsTerm v2 (substFormula v t f)

substFormula :: Variable -> Term -> Formula -> Formula
substFormula v t (PredForm p ts) = PredForm p (map (substTerm v t) ts)
substFormula v t (ForallForm v' f) = if v==v' then ForallForm v' f else ForallForm v' (substFormula v t f)
substFormula v t (ExistsForm v' f) = if v==v' then ExistsForm v' f else ExistsForm v' (substFormula v t f)
substFormula v t (ImpForm f1 f2) = ImpForm (substFormula v t f1) (substFormula v t f2)
substFormula v t (ConjForm f1 f2) = ConjForm (substFormula v t f1) (substFormula v t f2)
substFormula v t (DisjForm f1 f2) = DisjForm (substFormula v t f1) (substFormula v t f2)

alphaEqTerm :: Term -> Term -> Bool
alphaEqTerm (VarTerm v1) (VarTerm v2) = v1==v2
alphaEqTerm (AppTerm c1 ts1) (AppTerm c2 ts2) = c1==c2 && and (zipWith alphaEqTerm ts1 ts2)
alphaEqTerm (EpsTerm v1 f1) (EpsTerm v2 f2) = alphaEqFormula g1 g2
            where vs = termToVariables (EpsTerm v1 f1) `union` termToVariables (EpsTerm v2 f2)
                  u = variablesToFreshVariable vs
                  g1 = substFormula v1 (VarTerm u) f1
                  g2 = substFormula v2 (VarTerm u) f2
alphaEqTerm _ _ = False

alphaEqFormula :: Formula -> Formula -> Bool
alphaEqFormula (PredForm p1 ts1) (PredForm p2 ts2) = p1==p2 && and (zipWith alphaEqTerm ts1 ts2)
alphaEqFormula (ForallForm v1 f1) (ForallForm v2 f2) = alphaEqFormula g1 g2
               where vs = formulaToVariables (ForallForm v1 f1) `union` formulaToVariables (ForallForm v2 f2)
                     u = variablesToFreshVariable vs
                     g1 = substFormula v1 (VarTerm u) f1
                     g2 = substFormula v2 (VarTerm u) f2
alphaEqFormula (ExistsForm v1 f1) (ExistsForm v2 f2) = alphaEqFormula g1 g2
               where vs = formulaToVariables (ExistsForm v1 f1) `union` formulaToVariables (ExistsForm v2 f2)
                     u = variablesToFreshVariable vs
                     g1 = substFormula v1 (VarTerm u) f1
                     g2 = substFormula v2 (VarTerm u) f2
alphaEqFormula (ImpForm f1 g1) (ImpForm f2 g2) = alphaEqFormula f1 f2 && alphaEqFormula g1 g2
alphaEqFormula (ConjForm f1 g1) (ConjForm f2 g2) = alphaEqFormula f1 f2 && alphaEqFormula g1 g2
alphaEqFormula (DisjForm f1 g1) (DisjForm f2 g2) = alphaEqFormula f1 f2 && alphaEqFormula g1 g2
alphaEqFormula _ _ = False

termToSubterms :: Term -> [Term]
termToSubterms (VarTerm v) = [VarTerm v]
termToSubterms (AppTerm c ts) = [AppTerm c ts] `union` foldr (union . termToSubterms) [] ts
termToSubterms (EpsTerm v f) = [EpsTerm v f] `union` formulaToSubterms f

formulaToSubterms :: Formula -> [Term]
formulaToSubterms (PredForm p ts) = nub $ foldr (union . termToSubterms) [] ts
formulaToSubterms (ForallForm v f) = formulaToSubterms f
formulaToSubterms (ExistsForm v f) = formulaToSubterms f
formulaToSubterms (ImpForm f g) = unionBy alphaEqTerm (formulaToSubterms f) (formulaToSubterms g)
formulaToSubterms (ConjForm f g) = formulaToSubterms f `union` formulaToSubterms g
formulaToSubterms (DisjForm f g) = formulaToSubterms f `union` formulaToSubterms g

formulaToPredicates :: Formula -> [Predicate]
formulaToPredicates (PredForm p ts) = nub (p:concat (map termToPredicates ts))
formulaToPredicates (ImpForm f g) = formulaToPredicates f `union` formulaToPredicates g
formulaToPredicates (ConjForm f g) = formulaToPredicates f `union` formulaToPredicates g
formulaToPredicates (DisjForm f g) = formulaToPredicates f `union` formulaToPredicates g
formulaToPredicates (ForallForm v f) = formulaToPredicates f
formulaToPredicates (ExistsForm v f) = formulaToPredicates f

termToPredicates :: Term -> [Predicate]
termToPredicates (VarTerm _) = []
termToPredicates (AppTerm c ts) = nub $ concat $ map termToPredicates ts
termToPredicates (EpsTerm v f) = formulaToPredicates f

isPredicateVariable :: Predicate -> Bool
isPredicateVariable (Pred _ _ _) = True
isPredicateVariable _ = False

formulaToPredicateVariables :: Formula -> [Predicate]
formulaToPredicateVariables f = filter isPredicateVariable (formulaToPredicates f)

termToImmediateSubformula :: Term -> Maybe Formula
termToImmediateSubformula (VarTerm v) = Nothing
termToImmediateSubformula (AppTerm c ts) = Nothing
termToImmediateSubformula (EpsTerm v f) = Just f

falsity :: Formula
falsity = PredForm Falsum []

foldNegation :: Formula -> Formula
foldNegation (PredForm p ts) = PredForm p (map foldNegationAux ts)
foldNegation (ConjForm f f') = ConjForm (foldNegation f) (foldNegation f')
foldNegation (DisjForm f f') = DisjForm (foldNegation f) (foldNegation f')
foldNegation (ForallForm v f) = ForallForm v (foldNegation f)
foldNegation (ExistsForm v f) = ExistsForm v (foldNegation f)

foldNegationAux :: Term -> Term
foldNegationAux (VarTerm v) = VarTerm v
foldNegationAux (AppTerm c ts) = AppTerm c (map foldNegationAux ts)
foldNegationAux (EpsTerm v f) = EpsTerm v (foldNegation f)

unfoldNegation :: Formula -> Formula
unfoldNegation (PredForm p ts) = PredForm p (map unfoldNegationAux ts)
unfoldNegation (ImpForm f f') = ImpForm (unfoldNegation f) (unfoldNegation f')
unfoldNegation (ConjForm f f') = ConjForm (unfoldNegation f) (unfoldNegation f')
unfoldNegation (DisjForm f f') = DisjForm (unfoldNegation f) (unfoldNegation f')
unfoldNegation (ForallForm v f) = ForallForm v f
unfoldNegation (ExistsForm v f) = ExistsForm v f

unfoldNegationAux :: Term -> Term
unfoldNegationAux (VarTerm v) = VarTerm v
unfoldNegationAux (AppTerm c ts) = AppTerm c (map unfoldNegationAux ts)
unfoldNegationAux (EpsTerm v f) = EpsTerm v (unfoldNegation f)

epsTranslation :: Formula -> Formula
epsTranslation (ExistsForm v f) = substFormula v e f'
      where e = EpsTerm v f'
            f' = epsTranslation f
epsTranslation (ForallForm v f) = substFormula v e f'
      where e = EpsTerm v (makeNegForm f')
            f' = epsTranslation f
epsTranslation (PredForm p ts) = PredForm p ts
epsTranslation (ImpForm f g) = ImpForm (epsTranslation f) (epsTranslation g)
epsTranslation (ConjForm f g) = ConjForm (epsTranslation f) (epsTranslation g)
epsTranslation (DisjForm f g) = DisjForm (epsTranslation f) (epsTranslation g)

-- variableToString :: Variable -> String
-- variableToString (Var n i) = if i == -1 then n else n ++ show i

-- predicateToString :: Predicate -> String
-- --predicateToString Falsum = "⊥"
-- predicateToString Falsum = "bot"
-- predicateToString (Pred n i a) = if i == -1 then n else n ++ show i

-- formulaToString :: Formula -> String
-- formulaToString (PredForm p ts) = if null ts then pstr else pstr ++ "(" ++ intercalate "," (map termToString ts) ++ ")"
--       where pstr = predicateToString p
-- -- formulaToString (NegForm f) = "¬" ++ formulaToString f
-- -- formulaToString (ImpForm f g) = "(" ++ formulaToString f ++ "→" ++ formulaToString g ++ ")"
-- -- formulaToString (ConjForm f g) = "(" ++ formulaToString f ++ "∧" ++ formulaToString g ++ ")"
-- -- formulaToString (DisjForm f g) = "(" ++ formulaToString f ++ "∨" ++ formulaToString g ++ ")"
-- -- formulaToString (ForallForm v f) = "∀" ++ variableToString v ++ "(" ++ formulaToString f ++ ")"
-- -- formulaToString (ExistsForm v f) = "∃" ++ variableToString v ++ "(" ++ formulaToString f ++ ")"
-- formulaToString (NegForm f) = "~" ++ formulaToString f
-- formulaToString (ImpForm f g) = "(" ++ formulaToString f ++ " -> " ++ formulaToString g ++ ")"
-- formulaToString (ConjForm f g) = "(" ++ formulaToString f ++ " & " ++ formulaToString g ++ ")"
-- formulaToString (DisjForm f g) = "(" ++ formulaToString f ++ " | " ++ formulaToString g ++ ")"
-- formulaToString (ForallForm v f) = "all " ++ variableToString v ++ "(" ++ formulaToString f ++ ")"
-- formulaToString (ExistsForm v f) = "ex " ++ variableToString v ++ "(" ++ formulaToString f ++ ")"

-- constantToString :: Constant -> String
-- constantToString (Const n i a) = n ++ show i

-- termToString :: Term -> String
-- termToString (VarTerm v) = variableToString v
-- termToString (AppTerm c ts) = if null ts then cstr else cstr ++ "(" ++ intercalate "," (map termToString ts) ++ ")"
--       where cstr = constantToString c
-- --termToString (EpsTerm v f) = "ε" ++ variableToString v ++ "(" ++ formulaToString f ++ ")"
-- termToString (EpsTerm v f) = "eps " ++ variableToString v ++ "(" ++ formulaToString f ++ ")"

isImpForm :: Formula -> Bool
isImpForm (ImpForm _ _) = True
isImpForm _ = False

isDisjForm :: Formula -> Bool
isDisjForm (DisjForm _ _) = True
isDisjForm _ = False

isConjForm :: Formula -> Bool
isConjForm (ConjForm _ _) = True
isConjForm _ = False

isBiconForm :: Formula -> Bool
isBiconForm (PredForm p ts) = False
isBiconForm (ForallForm v f) = False
isBiconForm (ExistsForm v f) = False
isBiconForm (ImpForm f (PredForm Falsum [])) = False
isBiconForm _ = True

formulaInImpFormToPremise :: Formula -> Formula
formulaInImpFormToPremise (ImpForm f _) = f

makeKFormula :: Formula -> Formula -> Formula
makeKFormula f g = ImpForm f (ImpForm g f)

makeSFormula :: Formula -> Formula -> Formula -> Formula
makeSFormula f g h = ImpForm (ImpForm f (ImpForm g h)) (ImpForm (ImpForm f g) (ImpForm f h))
