module Syntax where
import Data.List(nub, delete, union, unionBy, intercalate, intersect)
import Utils
import Debug.Trace
import Data.Either

type Name = String
type Index = Int
type Arity = Int

data Variable = Var Name Index Arity deriving (Eq, Show, Ord)
data Constant = Const Name Index Arity deriving (Eq, Show)
data Term = VarTerm Variable | ConstTerm Constant | AppTerm Term Term | LamTerm [Variable] Term | EpsTerm Variable Formula deriving (Eq, Show)
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
variableToIndex (Var n i a) = i

variableToName :: Variable -> Name
variableToName (Var n i a) = n

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
comprehensionToKernel (Compr vs x) = x

comprehensionToKernelFormula :: Comprehension -> Formula
comprehensionToKernelFormula (Compr vs x) = x

-- comprehensionToKernelTerm :: Comprehension -> Term
-- comprehensionToKernelTerm (TermCompr vs x) = x

comprehensionToFreeVariables :: Comprehension -> [Variable]
--comprehensionToFreeVariables (TermCompr vs x) = foldr delete (termToFreeVariables x) vs
comprehensionToFreeVariables (Compr vs x) = foldr delete (formulaToFreeVariables x) vs

comprehensionToVariables :: Comprehension -> [Variable]
-- comprehensionToVariables (TermCompr vs x) = nub (vs ++ termToFreeVariables x)
comprehensionToVariables (Compr vs f) = nub (vs ++ formulaToFreeVariables f)

makeVariable :: Name -> Variable
makeVariable n = Var n (-1) 0

isVariable :: Variable -> Bool
isVariable (Var n i a) = not (null n) && i >= -1 && a >= 0

isConstant :: Constant -> Bool
isConstant (Const n i a) = not (null n) && i >= -1 && a >= 0

varTermToVar :: Term -> Variable
varTermToVar (VarTerm v) = v

variableToArity :: Variable -> Arity
variableToArity (Var n i a) = a

termToArity :: Term -> Arity
termToArity (VarTerm (Var n i a)) = a
termToArity (ConstTerm (Const n i a)) = a
termToArity (LamTerm vs t) = length vs
termToArity (AppTerm t1 t2) = termToArity t1 - 1

isTerm :: Term -> Bool
isTerm (VarTerm v) = isVariable v
--isTerm (AppTerm (Const n i a) ts) = isConstant (Const n i a) && (a == length ts) && all isTerm ts
isTerm (ConstTerm c) = isConstant c
isTerm (AppTerm t1 t2) = termToArity t1 >= 1 && isGroundTerm t2
isTerm (EpsTerm v f) = isFormula f

isVarTerm :: Term -> Bool
isVarTerm (VarTerm _) = True
isVarTerm _ = False

isGroundTerm :: Term -> Bool
isGroundTerm (VarTerm v) = variableToArity v == 0
isGroundTerm (ConstTerm c) = constantToArity c == 0
isGroundTerm (AppTerm t1 t2) = termToArity t1 == termToArity t2 +1
isGroundTerm (EpsTerm v f) = variableToArity v == 0

isEpsTerm :: Term -> Bool
isEpsTerm (EpsTerm v f) = isVariable v && isFormula f
isEpsTerm _ = False

epsTermToKernel :: Term -> Maybe Formula
epsTermToKernel (EpsTerm v f) = Just f
epsTermToKernel _ = Nothing

termToFreeVariables :: Term -> [Variable]
termToFreeVariables (VarTerm v) = [v]
termToFreeVariables (AppTerm t t') = nub (concat (map termToFreeVariables [t, t']))
termToFreeVariables (ConstTerm c) = []
termToFreeVariables (LamTerm vs t) = foldr delete (termToFreeVariables t) vs
termToFreeVariables (EpsTerm v f) = delete v (formulaToFreeVariables f)

termToVariables :: Term -> [Variable]
termToVariables (VarTerm v) = [v]
termToVariables (ConstTerm c) = []
termToVariables (LamTerm vs t) = nub $ vs ++ termToVariables t
termToVariables (AppTerm t t') = nub (concatMap termToVariables [t, t'])
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
variablesToFreshVariable [] = Var "x" 0 0
variablesToFreshVariable (v:vs) = Var (variableToName v) (maximum (map variableToIndex (v:vs)) + 1) 0

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

pvarAndTermToCriticalFormula :: Predicate -> Term -> Formula
pvarAndTermToCriticalFormula (Pvar n i 1) t = ImpForm (PredForm p [t]) (PredForm p [e])
      where p = Pvar n i 1
            v = Var "_" (-1) 0
            e = EpsTerm v (PredForm p [VarTerm v])

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
termToConstants (ConstTerm c) = [c]
termToConstants (LamTerm vs t) = termToConstants t
termToConstants (AppTerm t t') = concat (map termToConstants [t, t'])
termToConstants (EpsTerm v f) = formulaToConstants f

appTermToTerms :: Term -> [Term]
appTermToTerms (AppTerm t1 t2) = appTermToTerms t1 ++ [t2]
appTermToTerms t = [t]

termsToAppTerm :: [Term] -> Term
termsToAppTerm [t] = t
termsToAppTerm (t1:t2:ts) = termsToAppTerm (AppTerm t1 t2:ts)

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

lamTermAndArgsToTerm :: [Variable] -> Term -> [Term] -> Term
lamTermAndArgsToTerm forbVars (LamTerm [] kernel) [] = kernel
lamTermAndArgsToTerm forbVars (LamTerm (v:vs) kernel) (t:ts) =
      foldr (\(v, t) s -> termSubstitutionInTerm v t s) renamedKernel (zip freshVars (t:ts))
      where
            tFreeVars = termToFreeVariables t
            sFreeVars = termToFreeVariables kernel
            freshVars = variablesToFreshVariables (length (v:vs)) (filter (\v -> variableToArity v == 0) forbVars ++ sFreeVars ++ tFreeVars)
            renamedKernel = foldr (\(v, vt) s -> termSubstitutionInTerm v vt s) kernel (zip (v:vs) (map VarTerm freshVars))

termSubstitutionInTerm :: Variable -> Term -> Term -> Term
termSubstitutionInTerm v t targetTerm = termSubstitutionInTermAux forbVars v t targetTerm
      where
            forbVars = nub (v:termToVariables t++termToVariables targetTerm)

termSubstitutionInTermAux :: [Variable] -> Variable -> Term -> Term -> Term
termSubstitutionInTermAux forbVars v t (VarTerm v2) = if v==v2 then t else VarTerm v2
termSubstitutionInTermAux forbVars v t (ConstTerm c) = ConstTerm c
termSubstitutionInTermAux forbVars v (LamTerm vs t) (AppTerm t1 t2)
-- | alphaEqTerm hd (VarTerm v) = foldr (\(v, t) t' -> termSubstitutionInTerm v t t') t (zip vs args)
 | alphaEqTerm hd (VarTerm v) = lamTermAndArgsToTerm forbVars (LamTerm vs t) args
 | otherwise = AppTerm (termSubstitutionInTermAux forbVars v (LamTerm vs t) t1) (termSubstitutionInTermAux forbVars v (LamTerm vs t) t2)
      where
            ts = appTermToTerms (AppTerm t1 t2)
            hd = head ts
            args = tail ts
--(termSubstitutionInTermAux forbVars v t t1) (termSubstitutionInTermAux forbVars v t t2)
termSubstitutionInTermAux forbVars v t (AppTerm t1 t2) = AppTerm (termSubstitutionInTermAux forbVars v t t1) (termSubstitutionInTermAux forbVars v t t2)
termSubstitutionInTermAux forbVars v t (LamTerm vs t')
 | v `elem` vs = LamTerm vs t'
 | otherwise = LamTerm freshVs (termSubstitutionInTermAux forbVars' v t t'')
 where
      forbVars' = nub (forbVars ++ vs)
      freshVs = variablesToFreshVariables (length vs) (v:vs ++ forbVars' ++ termToFreeVariables t ++ termToFreeVariables t')
      t'' = foldr (\(v', s') s'' -> termSubstitutionInTerm v' s' s'') t' (zip vs (map VarTerm freshVs))
termSubstitutionInTermAux forbVars v t (EpsTerm v2 f)
  | v==v2 = EpsTerm v2 f
  | v2 `elem` termToFreeVariables t = let freshVar = variablesToFreshVariable (filter (\v -> variableToArity v == variableToArity v2) forbVars)
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
 where forbVars = nub (formulaToVariables f ++ formulaToVariables (comprehensionToKernelFormula c))

formulaSubstitutionInFormulaAux :: [Variable] -> Predicate -> Comprehension -> Formula -> Formula
formulaSubstitutionInFormulaAux forbVars p c (PredForm p' ts) = if p == p' && length ts == comprehensionToArity c
      then comprehensionAndTermsToFormula c ts'
      else PredForm p' (map (\t -> formulaSubstitutionInTermAux forbVars p c t) ts')
      where
            ts' = map (formulaSubstitutionInTermAux forbVars p c) ts
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
formulaSubstitutionInTermAux forbVars p c (ConstTerm cnst) = ConstTerm cnst
formulaSubstitutionInTermAux forbVars p c (AppTerm t1 t2) =
      AppTerm (formulaSubstitutionInTermAux forbVars p c t1) (formulaSubstitutionInTermAux forbVars p c t2)
formulaSubstitutionInTermAux forbVars p c (EpsTerm v f)
 | v `elem` comprehensionToFreeVariables c = let forbVars' = v:forbVars
                                                 freshVar = variablesToFreshVariable (filter (\u ->  variableToArity u == variableToArity v) forbVars')
                                                 freshVarTerm = VarTerm freshVar
                                                 f' = termSubstitutionInFormulaAux forbVars' v freshVarTerm f
                                              in EpsTerm freshVar (formulaSubstitutionInFormulaAux forbVars' p c f')
 | otherwise = EpsTerm v (formulaSubstitutionInFormulaAux (v:forbVars) p c f)
formulaSubstitutionInTermAux forbVars p c (LamTerm vs t)
 | null $ vs `intersect` comprehensionToFreeVariables c =
      let forbVars' = vs ++ forbVars
          freshVars = variablesToFreshVariables (length vs) forbVars'
          freshVarTerms = map VarTerm freshVars
          t' = foldr (\(v, s) s' -> termSubstitutionInTermAux forbVars' v s s') t (zip vs freshVarTerms)
        in LamTerm freshVars (formulaSubstitutionInTermAux forbVars' p c t')
 | otherwise = LamTerm vs (formulaSubstitutionInTermAux (vs++forbVars) p c t)

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
alphaEqTerm (AppTerm t1 t2) (AppTerm s1 s2) = alphaEqTerm t1 s1 && alphaEqTerm t2 s2
alphaEqTerm (ConstTerm c1) (ConstTerm c2) = c1 == c2
alphaEqTerm (LamTerm [] t) (LamTerm [] t') = alphaEqTerm t t'
alphaEqTerm (LamTerm (v:vs) t) (LamTerm (v':vs') t') = if v == v' then alphaEqTerm (LamTerm vs t) (LamTerm vs' t')
      else alphaEqTerm (LamTerm vs s) (LamTerm vs' s')
      where u = variablesToFreshVariable (termToVariables (LamTerm (v:vs) t) ++ termToVariables (LamTerm (v':vs') t'))
            uTerm = VarTerm u
            s = termSubstitutionInTerm v uTerm (LamTerm vs t)
            s' = termSubstitutionInTerm v' uTerm (LamTerm vs' t')
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
termToSubterms (AppTerm t1 t2) = [AppTerm t1 t2] `union` foldr (union . termToSubterms) [] [t1, t2]
termToSubterms (ConstTerm c) = [ConstTerm c]
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
termToPredicates (AppTerm t1 t2) = nub $ concat $ map termToPredicates [t1, t2]
termToPredicates (ConstTerm c) = []
termToPredicates (LamTerm vs t) = nub $ termToPredicates t
termToPredicates (EpsTerm v f) = formulaToPredicates f

isPredicateVariable :: Predicate -> Bool
isPredicateVariable (Pvar _ _ _) = True
isPredicateVariable _ = False

predicateFormToPredicate :: Formula -> Predicate
predicateFormToPredicate (PredForm p _) = p
predicateFormToPredicate _ = undefined

variablesAndArityToFreshVariables :: [Variable] -> Int -> Int -> [Variable]
variablesAndArityToFreshVariables knownVars arity number =
      map (\i -> Var "_" i arity) [i..i+number-1]
      where
            i = if null knownVars then 1 else maximum (map variableToIndex knownVars) + 1

formulaToImmediateSubTerms :: Formula -> [Term]
formulaToImmediateSubTerms = formulaToImmediateSubTermsAux []

formulaToImmediateSubTermsAux :: [Variable] -> Formula -> [Term]
formulaToImmediateSubTermsAux bvs (PredForm _ ts) =
      concatMap (\t -> if null $ bvs `intersect` termToFreeVariables t then [t] else termToImmediateSubTermsAux bvs t) ts
formulaToImmediateSubTermsAux bvs (ImpForm f g) = formulaToImmediateSubTermsAux bvs f ++ formulaToImmediateSubTermsAux bvs g
formulaToImmediateSubTermsAux bvs (ConjForm f g) = formulaToImmediateSubTermsAux bvs f ++ formulaToImmediateSubTermsAux bvs g
formulaToImmediateSubTermsAux bvs (DisjForm f g) = formulaToImmediateSubTermsAux bvs f ++ formulaToImmediateSubTermsAux bvs g
formulaToImmediateSubTermsAux bvs (ForallForm v f) = formulaToImmediateSubTermsAux [v] f
formulaToImmediateSubTermsAux bvs (ExistsForm v f) = formulaToImmediateSubTermsAux [v] f

termToImmediateSubTerms :: Term -> [Term]
termToImmediateSubTerms = termToImmediateSubTermsAux []

termToImmediateSubTermsAux :: [Variable] -> Term -> [Term]
termToImmediateSubTermsAux bvs (VarTerm v) = []
termToImmediateSubTermsAux bvs (ConstTerm c) = []
--termToImmediateSubTermsAux bvs (LamTerm vs t) =
termToImmediateSubTermsAux bvs (AppTerm t1 t2) =
      filter (\ t -> termToArity t == 0) ts'
      where
            ts = appTermToTerms (AppTerm t1 t2)
            ts' = concatMap (\t -> if null $ bvs `intersect` termToFreeVariables t then [t] else termToImmediateSubTermsAux bvs t) ts
termToImmediateSubTermsAux bvs (EpsTerm v f) = formulaToImmediateSubTermsAux (v:bvs) f

epsTermToEpsMatrixAuxFormula :: [Variable] -> Int -> Formula -> (Formula, Int)
epsTermToEpsMatrixAuxFormula bvs i (PredForm p ts) = (PredForm p ts', i')
      where f bvs i [] = ([], i)
            f bvs i (t:ts) = let (t', i') = epsTermToEpsMatrixAux bvs i t
                                 (rest, j) = f bvs i' ts
                              in (t':rest, j)
            (ts', i') = f bvs i ts
epsTermToEpsMatrixAuxFormula bvs i (ImpForm f g) = (ImpForm f' g', i'')
      where (f', i') = epsTermToEpsMatrixAuxFormula bvs i f
            (g', i'') = epsTermToEpsMatrixAuxFormula bvs i' g
epsTermToEpsMatrixAuxFormula bvs i (ConjForm f g) = (ConjForm f' g', i'')
      where (f', i') = epsTermToEpsMatrixAuxFormula bvs i f
            (g', i'') = epsTermToEpsMatrixAuxFormula bvs i' g
epsTermToEpsMatrixAuxFormula bvs i (DisjForm f g) = (DisjForm f' g', i'')
      where (f', i') = epsTermToEpsMatrixAuxFormula bvs i f
            (g', i'') = epsTermToEpsMatrixAuxFormula bvs i' g
epsTermToEpsMatrixAuxFormula bvs i (ForallForm v f) = (ForallForm v f', i')
      where (f', i') = epsTermToEpsMatrixAuxFormula (v:bvs) i f
epsTermToEpsMatrixAuxFormula bvs i (ExistsForm v f) = (ForallForm v f', i')
      where (f', i') = epsTermToEpsMatrixAuxFormula (v:bvs) i f

epsTermToEpsMatrix :: Term -> Term
epsTermToEpsMatrix (EpsTerm v f) = EpsTerm v f'
      where (f', i) = epsTermToEpsMatrixAuxFormula [v] (1+ (maximum $ map variableToIndex $ termToVariables (EpsTerm v f))) f

epsMatrixToClosedEpsMatrix :: Term -> Term
epsMatrixToClosedEpsMatrix e
 | isEpsTerm e && all isVarTerm iSubTerms && all (\t -> 0 == termToArity t) iSubTerms =
      if null absVars then e else LamTerm absVars e
 where
      iSubTerms = termToImmediateSubTerms e
      absVars = map varTermToVar iSubTerms

epsTermToEpsMatrixAux :: [Variable] -> Int -> Term -> (Term, Int)
epsTermToEpsMatrixAux bvs i (VarTerm v) = if v `elem` bvs then (VarTerm v, i) else (VarTerm (Var "_" i 0), i+1)
epsTermToEpsMatrixAux bvs i (ConstTerm c) = if constantToArity c == 0 then (VarTerm (Var "_" i 0), i+1) else (ConstTerm c, i)
--epsTermToEpsMatrixAux bvs (LamTerm vs t) =
epsTermToEpsMatrixAux bvs i (AppTerm t1 t2) = if null $ bvs `intersect` termToFreeVariables (AppTerm t1 t2)
                                                then (VarTerm (Var "_" i 0), i+1) else (termsToAppTerm ts', j)
      where
            f bvs i [] = ([], i)
            f bvs i (t:ts) = let (t', i') = epsTermToEpsMatrixAux bvs i t
                                 (rest, i'') = f bvs i' ts
                              in (t':rest, i'')
            ts = appTermToTerms (AppTerm t1 t2)
            (ts', j) = f bvs i ts
epsTermToEpsMatrixAux bvs i (EpsTerm v f) = if null $ bvs `intersect` termToFreeVariables (EpsTerm v f)
                                                then (VarTerm (Var "_" i 0), i+1) else (EpsTerm v f', i')
      where (f', i') = epsTermToEpsMatrixAuxFormula (v:bvs) i f

predicateVariablesAndArityToFreshPredicateVariable :: [Predicate] -> Int -> Predicate
predicateVariablesAndArityToFreshPredicateVariable [] a = Pvar "*" (-1) a
predicateVariablesAndArityToFreshPredicateVariable (p:ps) a
 | null preds = Pvar "*" (-1) a
 | otherwise = Pvar n i a
      where
            preds = filter (\p' -> predicateToArity p' == a) (p:ps)
            pred = head preds
            n = predicateToName pred
            i = 1+maximum (map predicateToIndex (p:ps))

predicateVariablesAndArityToFreshPredicateVariables :: [Predicate] -> Int -> Int -> [Predicate]
predicateVariablesAndArityToFreshPredicateVariables _ _ 0 = []
predicateVariablesAndArityToFreshPredicateVariables [] a n = map (\i -> Pvar "*" i a) [1..n]
predicateVariablesAndArityToFreshPredicateVariables ps a n
 | null relevantPvars = map (\i -> Pvar "*" i a) [1..n]
 | otherwise = newPvar:newPvars
      where
            relevantPvars = filter (\p -> predicateToArity p == a) ps
            newPvar = predicateVariablesAndArityToFreshPredicateVariable ps a
            newPvars = predicateVariablesAndArityToFreshPredicateVariables (newPvar:ps) a (n-1)

predicateVariablesAndAritiesToFreshPredicateVariables :: [Predicate] -> [Int] -> [Predicate]
predicateVariablesAndAritiesToFreshPredicateVariables _ [] = []
predicateVariablesAndAritiesToFreshPredicateVariables ps (a:as) = freshPvar:freshPvars
      where
            freshPvar = predicateVariablesAndArityToFreshPredicateVariable ps a
            freshPvars = predicateVariablesAndAritiesToFreshPredicateVariables (freshPvar:ps) as

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
foldNegationAux (AppTerm t1 t2) = AppTerm (foldNegationAux t1) (foldNegationAux t2)
foldNegationAux (ConstTerm c) = ConstTerm c
foldNegationAux (LamTerm vs t) = LamTerm vs (foldNegationAux t)
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
unfoldNegationAux (AppTerm t1 t2) = AppTerm (unfoldNegationAux t1) (unfoldNegationAux t2)
unfoldNegationAux (ConstTerm c) = ConstTerm c
unfoldNegationAux (LamTerm vs t) = LamTerm vs (unfoldNegationAux t)
unfoldNegationAux (EpsTerm v f) = EpsTerm v (unfoldNegation f)

formulasToImpFormula :: [Formula] -> Formula
formulasToImpFormula [x] = x
formulasToImpFormula (x:xs) = ImpForm x (formulasToImpFormula xs)

impFormulaAndNumberToFormulas :: Formula -> Int -> [Formula]
impFormulaAndNumberToFormulas f 0 = [f]
impFormulaAndNumberToFormulas (ImpForm f f') n = f:(impFormulaAndNumberToFormulas f' (n-1))

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

isPredForm :: Formula -> Bool
isPredForm (PredForm p _) = True
isPredForm _ = False

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

biconFormToSubFormulas :: Formula -> (Formula, Formula)
biconFormToSubFormulas (ImpForm f g) = (f, g)
biconFormToSubFormulas (ConjForm f g) = (f, g)
biconFormToSubFormulas (DisjForm f g) = (f, g)

isQuantForm :: Formula -> Bool
isQuantForm (ExistsForm _ _) = True
isQuantForm (ForallForm _ _) = True
isQuantForm _ = False

isForallForm :: Formula -> Bool
isForallForm (ForallForm _ _) = True
isForallForm _ = False

isExistsForm :: Formula -> Bool
isExistsForm (ExistsForm _ _) = True
isExistsForm _ = False

quantFormToVariableAndFormula :: Formula -> (Variable, Formula)
quantFormToVariableAndFormula (ForallForm v f) = (v, f)
quantFormToVariableAndFormula (ExistsForm v f) = (v, f)

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

formulaToFormulaWithFreshBoundVariables :: Formula -> [Variable] -> Formula
formulaToFormulaWithFreshBoundVariables (PredForm p ts) forbVars = PredForm p ts -- involved EpsTerm is to be consider
formulaToFormulaWithFreshBoundVariables (ImpForm f g) forbVars =
      ImpForm (formulaToFormulaWithFreshBoundVariables f forbVars) (formulaToFormulaWithFreshBoundVariables g forbVars)
formulaToFormulaWithFreshBoundVariables (ConjForm f g) forbVars =
      ConjForm (formulaToFormulaWithFreshBoundVariables f forbVars) (formulaToFormulaWithFreshBoundVariables g forbVars)
formulaToFormulaWithFreshBoundVariables (DisjForm f g) forbVars =
      DisjForm (formulaToFormulaWithFreshBoundVariables f forbVars) (formulaToFormulaWithFreshBoundVariables g forbVars)
formulaToFormulaWithFreshBoundVariables (ForallForm v f) forbVars =
      ForallForm u (formulaToFormulaWithFreshBoundVariables f' (u:v:forbVars))
      where u = variablesToFreshVariable (v:forbVars)
            f' = termSubstitutionInFormula v (VarTerm u) f
formulaToFormulaWithFreshBoundVariables (ExistsForm v f) forbVars =
      ExistsForm u (formulaToFormulaWithFreshBoundVariables f' (u:v:forbVars))
      where u = variablesToFreshVariable (v:forbVars)
            f' = termSubstitutionInFormula v (VarTerm u) f
