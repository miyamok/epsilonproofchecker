# epsilonproofchecker
Proof checker for Hilbert's epsilon calculus.
```
## ghc-9.2.8 used
% ghc Main
% ./Main ex04_identity.proof
Correct proof of
 ⊢ A -> A
% ./Main ex05_drinkers_paradox.proof
Correct proof of
 ⊢ P(eps x (P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x))
% ./Main ex06_wrong.proof
Not a proof of
A -> B
% ./Main ex08_assumption.proof 
Correct proof of
A ⊢ A
% 
```
## Epsilon calculus
Epsilon calculus is an extension of elementary calculus.  The language is enriched by the epsilon operator and an additional axiom so-called critical axiom is available.
Elementary calculus is propositional logic with predicates and terms in its language, maintaining the same principles for logical reasoning.

### Propositional calculus
For this moment, we restrict our base logic to the fragment of negation and implication.
Propositional formula F is defined as follows, where P<sub>0</sub> is ranging over propositional variables and A is an arbitrary element of P<sub>0</sub>.
```
F ::= A | bot | F -> F
```
The arrow denotes logical implication, and bot is a special constant denoting falsum.
The negated formula of A is written as follows using implication and falsum
```
A -> bot
```
and the formula
```
A -> bot
```
is abbreviated as
```
~A
```
which obviously means negation of A (namely, not A).
Let A, B, and C be atomic propositions in P.
The following three expressions are examples of propositional formulas.
```
A
A -> B
~A -> ~B -> B -> A
A -> B -> A
```
Here we assume negation has higher priority than implication, namely, the second formula above claims that if not A holds then B holds, but doesn't mean that it is not the case that A implies B.  Using parentheses, one can write a formula meaning that it is not the case that A implies B.
```
~(A -> B)
```
The third formula above claims that if not A holds, and also if not B holds, and also if B holds, then A holds.
If we supply (redundant) parentheses, it should look as
```
~A -> (~B -> (B -> A))
```
Implication in the right hand side has higher priority than the left, and we say that implication is right associative.
In order to mean that if not A implies not B, then B implies A, the use of parentheses is inevitable.
```
(~A -> ~B) -> B -> A
```
In order to give an objective explanation that a claim is true, one gives a proof to the claim.
A proof is a list of expressions, where an expression consists of a formula to claim and a reason of claiming it.
If there is a proof of A, we write
```
⊢A
```
A reason is either an axiom or an inference rule.  We have the following axioms
```
A -> B -> A
(A -> B -> C) -> (A -> B) -> A -> C
bot -> A
~~A -> A
```
and one inference rule.
```
If ⊢A -> B and ⊢A then ⊢B
```
Each of the above has the names K, S, EFQ, DNE, and MP, respectively.
K and S are traditional names, and the rest stands for ex falso quodlibet, double negation elimitaion, and modus ponens.
Note that the axioms are actually axiom schemas, namely, those propositional variables in the axiom formulas may be replaced by arbitrary formulas.  In order words, those occurrences of A, B, C are metavariables and diffrent from propositional variables, and those metavariables will be instantiated by concrete formulas in actual use.
Here we give a proof of the claim A implies A.
```
(A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A by S
A -> (A -> A) -> A by K
(A -> A -> A) -> A -> A by MP
A -> A -> A by K
A -> A by MP
```
For example in the second line, the axiom scheme K got its metavariable A replaced by a formula A, and another metavariable B replaced by a formula A -> A.
### Elementary calculus
Elementary calculus extends propositional calculus by terms and predicates for its language.
Let C<sub>0</sub> be a set of nullary constants, C<sub>1</sub> a set of unary (function) constants, and so, and let c and f be nullary and unary constants.  Let V be a set of variables.  Also, let Q be an element of P<sub>1</sub>, a set of unary atomic predicates.
Then the terms t and formulas F of elementary calculus is given as follows, assuming x a variable in V.
```
t ::= x | c | f(t)
F ::= A | Q(t) | bot | F -> F
```
Generally a formula E may contain a variable x.  In such a case, it is convenient to allow writing E(x) instead of E, and also allow writing E(t) for the formula obtained by replacing all occurrences of x in E by t.
Its axioms and inference rule are same as propositional calculus.
### Predicate calculus
(to be written)

### Epsilon calculus
Epsilon calculus extends elementary calculus by epsilon operator and so-called critical axiom.
Epsilon operator is denoted by eps and forming a term taking a variable and a formula.
The language definition of epsilon calculus is as follows.
```
t ::= c | f(t) | eps x F
F ::= A | Q(t) | bot | F -> F
```
A term of the form eps x E(x) is called epsilon term.  Intuitive meaning of an epsilon term eps x E(x) is the term which satisfies the property of x denoted by E(x).  Therefore, epsilon operator is often explained as a choice operator.
This intuition is formulated by the folliong critical axiom.
```
E(t) -> E(eps x E(x))
```
where t is an arbitrary term in epsilon calculus.
