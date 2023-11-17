module Syntax where
import Data.List(nub, delete, union, unionBy, intercalate, intersect)
import Utils
import Debug.Trace

type Name = String
type Index = Int
type Arity = Int

data Variable = Var Name Index deriving (Eq, Show, Ord)
data Constant = Const Name Index Arity deriving (Eq, Show)
data Term = VarTerm Variable | AppTerm Constant [Term] | EpsTerm Variable Formula deriving (Eq, Show)
data Predicate = Falsum | Equality | Pvar Name Index Arity deriving (Eq, Show)
data Formula = PredForm Predicate [Term] | ForallForm Variable Formula | ExistsForm Variable Formula |
               ImpForm Formula Formula | ConjForm Formula Formula  | DisjForm Formula Formula
               deriving (Eq, Show)
data Comprehension = Compr [Variable] Formula deriving (Show)

type VariableDeclaration = Name
type ConstantDeclaration = (Name, Int)
type PredicateDeclaration = (Name, Int)
type Declarations = ([VariableDeclaration], [ConstantDeclaration], [PredicateDeclaration])

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

declarationsToDeclarationsFilledWithDefaults :: Declarations -> Declarations
declarationsToDeclarationsFilledWithDefaults (vds, cds, pds) = (vds', cds', pds')
      where
            vds' = if null vds then defaultVariables else vds
            cds' = if null cds then defaultConstants else cds
            pds' = if null pds then defaultPredicates else pds

reservedNames :: [String]
reservedNames = ["Falsum", "Equality"]
-- reservedNames = ["by", "S", "K", "MP", "Gen", "ConjI", "ConjE1", "ConjE2", "DisjI1", "DisjI2", "DisjE",
--                  "AllE", "ExI", "DNE", "EFQ", "AllShift", "ExShift", "Auto", "Asm", "Ref", "C", "Use",
--                  "deduction-translation", "end-proof", "variables", "constants", "predicates"]

variableToIndex :: Variable -> Index
variableToIndex (Var n i) = i

variableToName :: Variable -> Name
variableToName (Var n i) = n

constantToArity :: Constant -> Arity
constantToArity (Const n i a) = a

predicateToName :: Predicate -> String
predicateToName (Pvar n i a) = n
predicateToName Falsum = "Falsum"
predicateToName Equality = "Equality"

predicateToIndex :: Predicate -> Index
predicateToIndex (Pvar n i a) = i
-- predicateToIndex Falsum = 0
-- predicateToIndex Equality = 0

predicateToArity :: Predicate -> Arity
predicateToArity (Pvar n i a) = a
predicateToArity Falsum = 0
predicateToArity Equality = 2

comprehensionToArity :: Comprehension -> Arity
comprehensionToArity (Compr vars _) = length vars

comprehensionToKernel :: Comprehension -> Formula
comprehensionToKernel (Compr vs f) = f

comprehensionToFreeVariables :: Comprehension -> [Variable]
comprehensionToFreeVariables (Compr vs f) = foldr delete (formulaToFreeVariables f) vs

comprehensionToVariables :: Comprehension -> [Variable]
comprehensionToVariables (Compr vs f) = nub (vs ++ formulaToFreeVariables f)

makeVariable :: Name -> Variable
makeVariable n = Var n (-1)

isVariable :: Variable -> Bool
isVariable (Var n i) = not (null n) && i >= -1

isConstant :: Constant -> Bool
isConstant (Const n i a) = not (null n) && i >= -1 && a >= 0

varTermToVar :: Term -> Variable
varTermToVar (VarTerm v) = v

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

variablesToFreshVariables :: Int -> [Variable] -> [Variable]
variablesToFreshVariables 0 knownVars = []
variablesToFreshVariables n knownVars = newVar:newVars
      where
            newVar = variablesToFreshVariable knownVars
            newVars = variablesToFreshVariables (n-1) (newVar:knownVars)

isPredicate :: Predicate -> Bool
isPredicate (Pvar n i a) = not (null n) && i >= -1 && a >= 0
isPredicate Falsum = True
isPredicate Equality = True

makePredicateVariable :: Name -> Arity -> Predicate
makePredicateVariable n a = Pvar n (-1) a

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
termToConstants (EpsTerm v f) = formulaToConstants f

makeNegFormula :: Formula -> Formula
makeNegFormula f = ImpForm f falsity

isNegFormula :: Formula -> Bool
isNegFormula (ImpForm _ (PredForm Falsum [])) = True
isNegFormula _ = False

isImpFormula :: Formula -> Bool
isImpFormula (ImpForm _ (PredForm Falsum [])) = False
isImpFormula (ImpForm _ _) = True
isImpFormula _ = False

isFormula :: Formula -> Bool
isFormula (PredForm p ts) = isPredicate p && predicateToArity p == length ts && all isTerm ts
isFormula (ForallForm v f) = isFormula f
isFormula (ExistsForm v f) = isFormula f
isFormula (ImpForm f1 f2) = isFormula f1 && isFormula f2
isFormula (ConjForm f1 f2) = isFormula f1 && isFormula f2
isFormula (DisjForm f1 f2) = isFormula f1 && isFormula f2

termSubstitutionInTerm :: Variable -> Term -> Term -> Term
termSubstitutionInTerm v t targetTerm = termSubstitutionInTermAux forbVars v t targetTerm
      where
            forbVars = nub (v:termToVariables t++termToVariables targetTerm)

termSubstitutionInTermAux :: [Variable] -> Variable -> Term -> Term -> Term
termSubstitutionInTermAux forbVars v t (VarTerm v2) = if v==v2 then t else VarTerm v2
termSubstitutionInTermAux forbVars v t (AppTerm c ts) = AppTerm c (map (termSubstitutionInTermAux forbVars v t) ts)
termSubstitutionInTermAux forbVars v t (EpsTerm v2 f)
  | v==v2 = EpsTerm v2 f
  | v2 `elem` termToFreeVariables t = let freshVar = variablesToFreshVariable forbVars
                                          freshVarTerm = VarTerm freshVar
                                          forbVars' = freshVar:forbVars
                                          f' = termSubstitutionInFormula v2 freshVarTerm f
                                       in EpsTerm freshVar (termSubstitutionInFormulaAux forbVars' v t f')
  | otherwise = EpsTerm v2 (termSubstitutionInFormulaAux forbVars v t f)

termSubstitutionInFormula :: Variable -> Term -> Formula -> Formula
termSubstitutionInFormula v t f = termSubstitutionInFormulaAux forbVars v t f
      where forbVars = nub (v:formulaToVariables f ++ termToVariables t)

termSubstitutionInFormulaAux :: [Variable] -> Variable -> Term -> Formula -> Formula
termSubstitutionInFormulaAux forbVars v t (PredForm p ts) = PredForm p (map (termSubstitutionInTermAux forbVars v t) ts)
termSubstitutionInFormulaAux forbVars v t (ForallForm v' f)
  | v==v' = ForallForm v' f
  | v' `elem` termToFreeVariables t = let freshVar = variablesToFreshVariable forbVars
                                          freshVarTerm = VarTerm freshVar
                                          forbVars' = freshVar:forbVars
                                          f' = termSubstitutionInFormula v' freshVarTerm f
                                       in ForallForm freshVar (termSubstitutionInFormulaAux forbVars' v t f')
  | otherwise = ForallForm v' (termSubstitutionInFormulaAux forbVars v t f)
termSubstitutionInFormulaAux forbVars v t (ExistsForm v' f)
  | v==v' = ExistsForm v' f
  | v' `elem` termToFreeVariables t = let freshVar = variablesToFreshVariable forbVars
                                          freshVarTerm = VarTerm freshVar
                                          forbVars' = freshVar:forbVars
                                          f' = termSubstitutionInFormula v' freshVarTerm f
                                       in ExistsForm freshVar (termSubstitutionInFormulaAux forbVars' v t f')
  | otherwise = ExistsForm v' (termSubstitutionInFormulaAux forbVars v t f)
termSubstitutionInFormulaAux forbVars v t (ImpForm f1 f2) = ImpForm (termSubstitutionInFormulaAux forbVars v t f1) (termSubstitutionInFormulaAux forbVars v t f2)
termSubstitutionInFormulaAux forbVars v t (ConjForm f1 f2) = ConjForm (termSubstitutionInFormulaAux forbVars v t f1) (termSubstitutionInFormulaAux forbVars v t f2)
termSubstitutionInFormulaAux forbVars v t (DisjForm f1 f2) = DisjForm (termSubstitutionInFormulaAux forbVars v t f1) (termSubstitutionInFormulaAux forbVars v t f2)

formulaSubstitutionInFormula :: Predicate -> Comprehension -> Formula -> Formula
formulaSubstitutionInFormula p c f
 | predicateToArity p == comprehensionToArity c = formulaSubstitutionInFormulaAux forbVars p c f
 | otherwise = undefined
 where forbVars = nub (formulaToVariables f ++ formulaToVariables (comprehensionToKernel c))

formulaSubstitutionInFormulaAux :: [Variable] -> Predicate -> Comprehension -> Formula -> Formula
formulaSubstitutionInFormulaAux forbVars p c (PredForm p' ts) = if p == p' && length ts == comprehensionToArity c
      then comprehensionAndTermsToFormula c ts
      else PredForm p' (map (\t -> formulaSubstitutionInTermAux forbVars p c t) ts)
formulaSubstitutionInFormulaAux forbVars p c (ImpForm f g) = ImpForm f' g'
      where f' = formulaSubstitutionInFormulaAux forbVars p c f
            g' = formulaSubstitutionInFormulaAux forbVars p c g
formulaSubstitutionInFormulaAux forbVars p c (ConjForm f g) = ConjForm f' g'
      where f' = formulaSubstitutionInFormulaAux forbVars p c f
            g' = formulaSubstitutionInFormulaAux forbVars p c g
formulaSubstitutionInFormulaAux forbVars p c (DisjForm f g) = DisjForm f' g'
      where f' = formulaSubstitutionInFormulaAux forbVars p c f
            g' = formulaSubstitutionInFormulaAux forbVars p c g
formulaSubstitutionInFormulaAux forbVars p c (ForallForm v f)
      | v `elem` comprehensionToFreeVariables c = let forbVars' = v:forbVars
                                                      freshVar = variablesToFreshVariable forbVars'
                                                      freshVarTerm = VarTerm freshVar
                                                      f' = termSubstitutionInFormulaAux forbVars' v freshVarTerm f
                                                   in ForallForm freshVar (formulaSubstitutionInFormulaAux forbVars' p c f')
      | otherwise = ForallForm v (formulaSubstitutionInFormulaAux (v:forbVars) p c f)
formulaSubstitutionInFormulaAux forbVars p c (ExistsForm v f)
      | v `elem` comprehensionToFreeVariables c = let forbVars' = v:forbVars
                                                      freshVar = variablesToFreshVariable forbVars'
                                                      freshVarTerm = VarTerm freshVar
                                                      f' = termSubstitutionInFormulaAux forbVars' v freshVarTerm f
                                                   in ExistsForm freshVar (formulaSubstitutionInFormulaAux forbVars' p c f')
      | otherwise = ExistsForm v (formulaSubstitutionInFormulaAux (v:forbVars) p c f)

formulaSubstitutionInTerm :: Predicate -> Comprehension -> Term -> Term
formulaSubstitutionInTerm p c t
 | predicateToArity p == comprehensionToArity c = formulaSubstitutionInTermAux forbVars p c t
 | otherwise = undefined
 where forbVars = nub (termToVariables t ++ comprehensionToVariables c)

formulaSubstitutionInTermAux :: [Variable] -> Predicate -> Comprehension -> Term -> Term
formulaSubstitutionInTermAux forbVars p c (VarTerm v) = VarTerm v
formulaSubstitutionInTermAux forbVars p c (AppTerm c' ts) = AppTerm c' (map (formulaSubstitutionInTermAux forbVars p c) ts)
formulaSubstitutionInTermAux forbVars p c (EpsTerm v f)
 | v `elem` comprehensionToFreeVariables c = let forbVars' = v:forbVars
                                                 freshVar = variablesToFreshVariable forbVars'
                                                 freshVarTerm = VarTerm freshVar
                                                 f' = termSubstitutionInFormulaAux forbVars' v freshVarTerm f
                                              in EpsTerm freshVar (formulaSubstitutionInFormulaAux forbVars' p c f')
 | otherwise = EpsTerm v (formulaSubstitutionInFormulaAux (v:forbVars) p c f)

comprehensionAndTermsToFormula :: Comprehension -> [Term] -> Formula
comprehensionAndTermsToFormula (Compr [] kernel) [] = kernel
comprehensionAndTermsToFormula (Compr (v:vs) kernel) (t:ts)
 | v `elem` vs = comprehensionAndTermsToFormula (Compr vs kernel) ts
 | null (vs `intersect` termToFreeVariables t) = comprehensionAndTermsToFormula (Compr vs (termSubstitutionInFormula v t kernel)) ts
 | otherwise = let forbVars = nub (termToVariables t ++ formulaToVariables kernel ++ (v:vs))
                   freshVars = variablesToFreshVariables (length vs) forbVars
                   freshVarTerms = map VarTerm freshVars
                   renamedKernel = foldr (\(v, t) f -> termSubstitutionInFormula v t f) kernel (zip vs freshVarTerms)
                in comprehensionAndTermsToFormula (Compr freshVars (termSubstitutionInFormula v t renamedKernel)) ts

alphaEqTerm :: Term -> Term -> Bool
alphaEqTerm (VarTerm v1) (VarTerm v2) = v1==v2
alphaEqTerm (AppTerm c1 ts1) (AppTerm c2 ts2) = c1==c2 && and (zipWith alphaEqTerm ts1 ts2)
alphaEqTerm (EpsTerm v1 f1) (EpsTerm v2 f2) = alphaEqFormula g1 g2
            where vs = termToVariables (EpsTerm v1 f1) `union` termToVariables (EpsTerm v2 f2)
                  u = variablesToFreshVariable vs
                  g1 = termSubstitutionInFormula v1 (VarTerm u) f1
                  g2 = termSubstitutionInFormula v2 (VarTerm u) f2
alphaEqTerm _ _ = False

alphaEqFormula :: Formula -> Formula -> Bool
alphaEqFormula (PredForm p1 ts1) (PredForm p2 ts2) = p1==p2 && and (zipWith alphaEqTerm ts1 ts2)
alphaEqFormula (ForallForm v1 f1) (ForallForm v2 f2) = alphaEqFormula g1 g2
               where vs = formulaToVariables (ForallForm v1 f1) `union` formulaToVariables (ForallForm v2 f2)
                     u = variablesToFreshVariable vs
                     g1 = termSubstitutionInFormula v1 (VarTerm u) f1
                     g2 = termSubstitutionInFormula v2 (VarTerm u) f2
alphaEqFormula (ExistsForm v1 f1) (ExistsForm v2 f2) = alphaEqFormula g1 g2
               where vs = formulaToVariables (ExistsForm v1 f1) `union` formulaToVariables (ExistsForm v2 f2)
                     u = variablesToFreshVariable vs
                     g1 = termSubstitutionInFormula v1 (VarTerm u) f1
                     g2 = termSubstitutionInFormula v2 (VarTerm u) f2
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
isPredicateVariable (Pvar _ _ _) = True
isPredicateVariable _ = False

predicateFormToPredicate :: Formula -> Predicate
predicateFormToPredicate (PredForm p _) = p
predicateFormToPredicate _ = undefined

predicateVariablesToFreshPredicateVariable :: [Predicate] -> Predicate
predicateVariablesToFreshPredicateVariable [] = undefined
predicateVariablesToFreshPredicateVariable (p:ps)
 | allEqual $ map predicateToArity (p:ps) = let a = predicateToArity p
                                                n = predicateToName p
                                                i = 1+maximum (map predicateToIndex (filter (\p -> predicateToName p == n) (p:ps)))
                                          in Pvar n i a
 | otherwise = undefined

predicateVariablesToFreshPredicateVariables :: Int -> [Predicate] -> [Predicate]
predicateVariablesToFreshPredicateVariables 0 _ = []
predicateVariablesToFreshPredicateVariables n ps = newPred:newPreds
      where
            newPred = predicateVariablesToFreshPredicateVariable ps
            newPreds = predicateVariablesToFreshPredicateVariables (n-1) (newPred:ps)

predicateVariablesAndArityToFreshPredicateVariable :: [Predicate] -> Int -> Predicate
predicateVariablesAndArityToFreshPredicateVariable [] a = undefined
predicateVariablesAndArityToFreshPredicateVariable (p:ps) a
 | null preds = undefined
 | otherwise =  Pvar n i a
      where
            preds = filter (\p -> predicateToArity p == a) (p:ps)
            pred = head preds
            n = predicateToName p
            i = 1+maximum (map predicateToIndex preds)

predicateVariablesAndArityToFreshPredicateVariables :: Int -> [Predicate] -> Int -> [Predicate]
predicateVariablesAndArityToFreshPredicateVariables _ [] _ = undefined
predicateVariablesAndArityToFreshPredicateVariables n ps a
 | null relevantPvars = undefined
 | otherwise = newPvar:newPvars
      where
            relevantPvars = filter (\p -> predicateToArity p == a) ps
            newPvar = predicateVariablesAndArityToFreshPredicateVariable ps a
            newPvars = predicateVariablesAndArityToFreshPredicateVariables (n-1) (newPvar:ps) a

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
epsTranslation (ExistsForm v f) = termSubstitutionInFormula v e f'
      where e = EpsTerm v f'
            f' = epsTranslation f
epsTranslation (ForallForm v f) = termSubstitutionInFormula v e f'
      where e = EpsTerm v (makeNegFormula f')
            f' = epsTranslation f
epsTranslation (PredForm p ts) = PredForm p ts
epsTranslation (ImpForm f g) = ImpForm (epsTranslation f) (epsTranslation g)
epsTranslation (ConjForm f g) = ConjForm (epsTranslation f) (epsTranslation g)
epsTranslation (DisjForm f g) = DisjForm (epsTranslation f) (epsTranslation g)

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

declarationsToConflictingIdentifierNames :: Declarations -> [Name]
declarationsToConflictingIdentifierNames (vds, cds, pds) =
      if null doubledNames then [] else doubledNames
      where
            vnames = if null vds then defaultVariables else vds
            cnames = map fst (if null cds then defaultConstants else cds)
            pnames = map fst (if null pds then defaultPredicates else pds)
            doubledNames = doubles (vnames ++ cnames ++ pnames)
