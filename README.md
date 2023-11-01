# epsilon --- a proof checker for Hilbert's epsilon calculus
Proof checker for Hilbert's epsilon calculus.
```
## ghc-9.2.8 used
% ghc Main
% ./Main examples/ex04_identity.proof
Correct proof of
 ⊢ A -> A
% cat examples/ex04_identity.proof 
A -> (A -> A) -> A by K
A -> A -> A by K
(A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A by S
(A -> A -> A) -> A -> A by MP
A -> A by MP
% ./Main examples/ex05_drinkers_paradox.proof
Correct proof of
 ⊢ P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x))
% ./Main examples/ex06_wrong.proof
Not a proof of
A -> B
% ./Main examples/ex08_assumption.proof 
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
If a proof of <code>A</code> comes with assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>, we write
```
A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A
```
and it means that <code>A</code> is proved under the condions that <code>A<sub>1</sub>, ..., A<sub>k</sub></code> are all true.
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
Predicate caluclus is an extension of elementary calculus by quantifications.
The language is enriched by the existential quantifier and the universal quantifier.  The syntax is given as follows.
```
t ::= x | c | f(t)
F ::= A | Q(t) | bot | F -> F | ex x F | all x F
```
Assume E(x) is a formula containing a free variable x.  One interpretation of this formula is that it states some property of x.
By means of the quantifiers, it is possible to form the following quantified formulas.
```
ex x E(x)
all x E(x)
```
They denote that there is some x such that E(x) holds, and that for any x, E(x) holds.

We have two kinds of variable occurrences due to the presence of the quantifiers.
Assume a formula <code>E(x)</code> is free from a quantifier and <code>x</code> has at least one occurrences in <code>E(x)</code>.
In the formula <code>all x E(x)</code>, all the occurrences of <code>x</code> is bounded, while all the occurrences of <code>x</code> in <code>E(x)</code> is free.
This variable binding mechanism is important to formulate the logic of predicate calculus, and the definition of free varialbles <code>FV</code> is given as follows.
```
FV(x) = {x}
FV(f(t)) = FV(t)
FV(eps x E(x)) = FV(E(x)) - {x}
FV(bot) = {}
FV(P(t)) = FV(t)
FV(A -> B) = FV(A) ∪ FV(B)
FV(A & B) = FV(A) ∪ FV(B)
FV(A | B) = FV(A) ∪ FV(B)
FV(all x E(x)) = FV(E(x)) - {x}
FV(ex x E(x)) = FV(E(x)) - {x}
```
From now on, if we write a formula in the form <code>A(x)</code>, it means that <code>x</code> may occur freely in <code>A(x)</code>, however, it is not the case that a bound variable <code>x</code> is indicated in this notation.
Moreover, a change of bound variable names doesn't affect the meaning of formulas and terms.
Consider a formula <code>A(x)</code> which does not have a free occurrence of variables other than <code>x</code>.
Then, <code>ex x A(x)</code> is equivalent as <code>ex y A(y)</code> for any variable <code>y</code>.
This is same as the fact that formal argument names of a function definition are changeable without modifying the meaning of the function.
It also requires a delicate treatment of the substitution, that is, by replacing <code>x</code> in <code>A(x)</code> by <code>t</code>, we should avoid to get any free variable in <code>t</code> newly captured.  We assume bound variables in <code>A(x)</code> are properly renamed before the operation of substitution, so that there is no free variable in <code>t</code> which is bound in <code>A(t)</code>.  For example, let a formula <code>A(x)</code> be <code>ex y (P(x) & P(y))</code>.  Apparently, the occurrence of <code>x</code> is free and the ones of <code>y</code> are bound.  In case we consider a substitution <code>A(y)</code>, we cannot simply replace <code>x</code> in <code>ex y (P(x) & P(y))</code> by <code>y</code> to get <code>ex y (P(y) & P(y))</code>.  The right way to do the substitution is that we rename the bound variable <code>y</code> in <code>A(y)</code> before the replacement, for example by using a fresh variable <code>z</code>, we form a logically equivalent formula <code>ex z (P(x) & P(z))</code>, and perform the replacement to get <code>ex z (P(y) & P(z))</code>.

In order to reason about formulas involving the quantifiers, predicate calculus employs additional 4 axioms and 1 inference rule.
```
all x A(x) -> A(t)
A(t) -> ex x A(x)
all x(B -> A(x)) -> (B -> all y A(y))
all x(A(x) -> B) -> (ex y A(y) -> B)
```
Here we assumed <code>x</code> does not have a free occurrence in <code>B</code>, and also if <code>x</code> is distinct variable from <code>y</code>, then <code>y</code> doesn't have a free occurrence in <code>A(x)</code>.
The new inference rule is called the rule of generalization, which allows to derive <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ all x E(x)</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ E(x)</code> under the condition that <code>x</code> does not have a free occurrence in <code>A<sub>1</sub>, ..., A<sub>k</sub></code> and also that if <code>x</code> is distinct variable from <code>y</code>, then <code>y</code> doesn't have a free occurrence in <code>A(x)</code>.
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
Epsilon operator is expressive enough to define the existential and universal quantifiers of predicate logic.
Let E(x) be a formula, then the corresponding quantified formulas are defined as follows. 
```
ex x E(x) := E(eps x E(x))
all x E(x) := E(eps x ~E(x))
```
We are going to look at examples.
The following formula is known as independence of premise, where the formula A does not contain a free variable x.
```
(A -> ex x P(x)) -> ex x (A -> P(x))
```
Applying the definition of the existential quantifier by epsilon operator, the above formula goes to the following one.
```
(A -> P(eps x P(x))) -> A -> B(eps x(A -> P(x)))
```
A proof to this formula is given in examples/ex01_ex01_independence_of_premise.proof .
```
(A -> P(eps x P(x))) -> A -> P(eps x (A -> P(x))) by C
```
Notice that this formula is an instance of the critical axiom.
Another examples is a so-called Drinker's paradox.
```
ex x(P(x) -> all x P(x))
```
The meaning of this provable formula is often explained through a story of a pub, that is, there is a guy in a pub such that if the guy is drinking then everybody in the pub is drinking.
This claim may sound a bit confusing, and this is the reason why this formula is called a paradox.  If there is a guy in the pub who is not drinking, you pick this guy, then the premise of the implication goes false, hence the whole formula is true.  Otherwise everybody is drinking, hence you can pick an arbitrary guy.  In case of a real pub, it is decidable whether there is a guy who is not drinking.  This formula is true even in case the matter is undecidable.
The epsilon version of the above formula is
```
P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x))
```
A proof is given in examples/ex05_drinkers_paradox.proof
After proving the identity formula P(eps x ~P(x)) -> P(eps x ~P(x)), the rest of the proof goes as follows.
```
(P(eps x ~P(x)) -> P(eps x ~P(x))) -> P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by C
P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by MP
```
## Syntax for proof scripts
Epsilonproofchecker processes a proof script which is stored as a file in the system.
A proof script is a list of proof steps, each of which consists of the following ingredients.
1. A formula to claim
2. A reason of claiming the formula
3. Optional tag for future reference to this proof step
Formula is what we saw in the previous section of this documentation.
A reason is either a name of an axiom, an assumption, or an inference rule which may come with an additional parameters.
A tag is a reference name, which is a string starting with #, given to the proof step, which can be used to point this proof step later on.
Assume E(x) is a formula and R is some name of axiom or inference rule, the syntax of the proof step is given as follows
```
E(x) by R
```
and also one can give a tag to this proof step.
```
E(x) by R #myproofstep
```
Epsilonproofchecker supports the following axioms.

Axiom name | Scheme | Note
--- | --- | ---
<code>S</code> | <code>(A -> B -> C) -> (A -> B) -> A -> C</code> | <code>-></code> is left associative
<code>K</code> | <code>A -> B -> A</code>
<code>C</code> | <code>E(t) -> E(eps x E(x))</code> | <code>t</code> is an arbitrary term in this whole table
<code>ConjI</code> | <code>A -> B -> A & B</code> | <code>&</code> is right associative and has a higher priority than <code>-></code>
<code>ConjE1</code> | <code>A & B -> A</code>
<code>ConjE2</code> | <code>A & B -> B</code>
<code>DisjI1</code> | <code>A -> A \| B</code> | <code>\|</code> is right associative and has a priority between <code>-></code> and <code>&</code>
<code>DisjI2</code> | <code>B -> A \| B</code>
<code>DisjE</code> | <code>A \| B -> (A -> C) -> (B -> C) -> C</code>
<code>AllE</code> | <code>all x E(x) -> E(t)</code>
<code>ExI</code> | <code>E(t) -> ex x E(x)</code>
<code>AllShift</code> | <code>all x(B -> A(x)) -> (B -> all y A(y))</code> | x ∉ FV(B) and (x=y or y ∉ FV(A(x)))
<code>ExShift</code> | <code>all x(A(x) -> B) -> (ex y A(y) -> B)</code> | x ∉ FV(B) and (x=y or y ∉ FV(A(x)))
<code>EFQ</code> | <code>bot -> A</code>
<code>DNE</code> | <code>~~A -> A</code> | <code>~</code> has a higher priority than any of <code>-></code>, <code>\|</code> and <code>&</code>

In order to pose an assumption, <code>Asm</code> is used as the reason.  Whereever the assumption is witten in the proof, either top, middle, or the bottom, it does not make any difference.
If a proof comes with assumptions, those assumptions are displayed in the left hand side of <code>⊢</code>

The inference rule <code>MP</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ B</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A -> B</code> and <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A</code>, two of which should be somewhere in previous proof steps.
The inference rule <code>Gen</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ all x E(x)</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ E(x)</code> which should be a previous proof step, under the condition that <code>x</code> doesn't have a free occurrrence in any of the assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
The search for suitable proof steps for those inference rules is done automatically.
Note that the formula <code>A</code> is distinct from any indexed ones <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
If one wants to explicitly specify the two proof steps, tagged by <code>#one</code> and <code>#two</code>, the arguments should be fed as <code>MP(#one, #two)</code>, which is order insensitive.

Example proofs are found in the <code>examples</code> directory, which cover all of the above mentioned features.
