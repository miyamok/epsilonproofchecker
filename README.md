# epsilon --- a proof checker for Hilbert's epsilon calculus
Proof checker for Hilbert's epsilon calculus.  It supports Hilbert style proofs in epsilon calculus as well as in first order predicate calculus.
##### Table of contents
- [Logic](#logic)
  - [Propositional calculus](#prop)
  - [Elementary calculus](#elem)
  - [Predicate calculus](#pred)
  - [Epsilon calculus](#eps)
- [Syntax for proof scripts](#syntax)
- [To do list](#todo)
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
<a name="logic"/>
## Logic
Epsilon calculus is an extension of elementary calculus.  The language is enriched by the epsilon operator and an additional axiom so-called critical axiom is available.
Elementary calculus is propositional logic with predicates and terms in its language, maintaining the same principles for logical reasoning.
<a name="prop"/>
### Propositional calculus
For this moment, we restrict our base logic to the fragment of negation and implication.
Propositional formula <code>F</code> is defined as follows, where <code>P<sub>0</sub></code> is ranging over propositional variables and <code>A</code> is an arbitrary element of <code>P<sub>0</sub></code>.
```
F ::= A | bot | F -> F
```
The arrow denotes logical implication, and bot is a special constant denoting falsum.
The negated formula of <code>A</code> is written as follows using implication and falsum
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
which means negation of <code>A</code> (namely, not <code>A</code>).
Let <code>A</code>, <code>B</code>, and <code>C</code> be atomic propositions in <code>P</code>.
The following three expressions are examples of propositional formulas.
```
A
A -> B
~A -> ~B -> B -> A
A -> B -> A
```
Here we assume negation has higher priority than implication, namely, the second formula above claims that if not <code>A</code> holds then <code>B</code> holds, but doesn't mean that it is not the case that <code>A</code> implies <code>B</code>.  Using parentheses, one can write a formula meaning that it is not the case that <code>A</code> implies <code>B</code>.
```
~(A -> B)
```
The third formula above claims that if not <code>A</code> holds, and also if not <code>B</code> holds, and also if <code>B</code> holds, then <code>A</code> holds.
If we supply (redundant) parentheses, it should look as
```
~A -> (~B -> (B -> A))
```
Implication in the right hand side has higher priority than the left, and we say that implication is right associative.
In order to mean that if not <code>A</code> implies not <code>B</code>, then <code>B</code> implies <code>A</code>, the use of parentheses is inevitable.
```
(~A -> ~B) -> B -> A
```
In order to give an objective explanation that a claim is true, one gives a proof to the claim.
A proof is a list of expressions, where an expression consists of a formula to claim and a reason of claiming it.
If there is a proof of <code>A</code>, we write
```
⊢A
```
If a proof shows <code>A</code> from assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>, we write
<code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A</code>
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
Each of the above has the names <code>K</code>, <code>S</code>, <code>EFQ</code>, <code>DNE</code>, and <code>MP</code>, respectively.
<code>K</code> and <code>S</code> are traditional names, and the rest stands for ex falso quodlibet, double negation elimitaion, and modus ponens.
Note that the axioms are actually axiom schemas, namely, those propositional variables in the axiom formulas may be replaced by arbitrary formulas.  In order words, those occurrences of <code>A</code>, <code>B</code>, <code>C</code> are metavariables and diffrent from propositional variables, and those metavariables will be instantiated by concrete formulas in actual use.
Here we give a proof of the claim <code>A</code> implies <code>A</code>.
```
(A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A by S
A -> (A -> A) -> A by K
(A -> A -> A) -> A -> A by MP
A -> A -> A by K
A -> A by MP
```
For example in the second line, the axiom scheme <code>K</code> got its metavariable <code>A</code> replaced by a formula <code>A</code>, and another metavariable <code>B</code> replaced by a formula <code>A -> A</code>.

Now we get rid of the limitation of our language, and see not only implication and negation but also conjunction and disjunction.
The grammar of the language of propositional calculus is defined as follows.
```
F ::= A | bot | F -> F | F & F | (F | F)
```
The vertical line is used for both the BNF syntax notation and our logical language, hence parentheses are inserted to make the matter a bit clear.
A conjunction formula <code>A & B</code> claims that <code>A</code> and <code>B</code> hold.
A disjunction formula <code>A | B</code> claims that <code>A</code> or <code>B</code> hold.  Note that the disjunction doesn't mean that there is a possibility of both <code>A</code> and <code>B</code> hold.

The way of reasoning with conjunction and disjunction is described in the next section, Syntax for proof scripts.
<a name="elem"/>
### Elementary calculus
Elementary calculus extends propositional calculus by terms and predicates for its language.
Let <code>C<sub>0</sub></code> be a set of nullary constants, <code>C<sub>1</sub></code> a set of unary (function) constants, and so, and let <code>c</code> and <code>f</code> be nullary and unary constants.  Let <code>V</code> be a set of variables.  Also, let <code>Q</code> be an element of <code>P<sub>1</sub></code>, a set of unary atomic predicates.
Then the terms <code>t</code> and formulas <code>F</code> of elementary calculus is given as follows, assuming <code>x</code> a variable in <code>V</code>.
```
t ::= x | c | f(t)
F ::= ... | Q(t)
```
Generally a formula <code>E</code> may contain a variable <code>x</code>.  In such a case, it is convenient to allow writing <code>E(x)</code> instead of <code>E</code>, and also allow writing <code>E(t)</code> for the formula obtained by replacing all occurrences of <code>x</code> in <code>E</code> by <code>t</code>.
Its axioms and inference rule are same as propositional calculus.
<a name="pred"/>
### Predicate calculus
Predicate caluclus is an extension of elementary calculus by quantifications.
The language is enriched by the existential quantifier and the universal quantifier.  The syntax is given as follows.
```
t ::= ...
F ::= ... | ex x F | all x F
```
Assume <code>E(x)</code> is a formula containing a free variable x.  One interpretation of this formula is that it states some property of <code>x</code>.
By means of the quantifiers, it is possible to form the following quantified formulas.
```
ex x E(x)
all x E(x)
```
They denote that there is some <code>x</code> such that <code>E(x)</code> holds, and that for any <code>x</code>, <code>E(x)</code> holds.

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
<a name="eps"/>
### Epsilon calculus
Epsilon calculus extends elementary calculus by epsilon operator and so-called critical axiom.
Epsilon operator is denoted by eps and forming a term taking a variable and a formula.
The language definition of epsilon calculus is as follows.
```
t ::= ... | eps x F
F ::= ... 
```
A term of the form <code>eps x E(x)</code> is called epsilon term.  Intuitive meaning of an epsilon term <code>eps x E(x)</code> is the term which satisfies the property of <code>x</code> denoted by <code>E(x)</code>.  Therefore, epsilon operator is often explained as a choice operator.
This intuition is formulated by the folliong critical axiom.
```
E(t) -> E(eps x E(x))
```
where <code>t</code> is an arbitrary term in epsilon calculus.
Epsilon operator is expressive enough to define the existential and universal quantifiers of predicate logic.
Let <code>E(x)</code> be a formula, then the corresponding quantified formulas are defined as follows. 
```
ex x E(x) := E(eps x E(x))
all x E(x) := E(eps x ~E(x))
```
We are going to look at examples.
The following formula is known as independence of premise, where the formula <code>A</code> does not contain a free variable <code>x</code>.
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
After proving the identity formula <code>P(eps x ~P(x)) -> P(eps x ~P(x))</code>, the rest of the proof goes as follows.
```
(P(eps x ~P(x)) -> P(eps x ~P(x))) -> P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by C
P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by MP
```
<a name="syntax"/>
## Syntax for proof scripts
Epsilonproofchecker processes a proof script which is stored as a file in the system.
A proof script is a list of proof steps, each of which consists of the following ingredients.
1. A formula to claim
2. A reason of claiming the formula
3. Optional tag for future reference to this proof step

Formula is what we saw in the previous section of this documentation.
A reason is either a name of an axiom, an assumption, or an inference rule which may come with an additional parameters.
A tag is a reference name, which is a string starting with <code>#</code>, given to the proof step, which can be used to point this proof step later on.
Assume <code>E(x)</code> is a formula and R is some name of axiom or inference rule, the syntax of the proof step is given as follows
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
<code>AllShift</code> | <code>all x(B -> A(x)) -> (B -> all y A(y))</code> | <code>x ∉ FV(B)</code> and (<code>x=y</code> or <code>y ∉ FV(A(x))</code>)
<code>ExShift</code> | <code>all x(A(x) -> B) -> (ex y A(y) -> B)</code> | <code>x ∉ FV(B)</code> and (<code>x=y</code> or <code>y ∉ FV(A(x))</code>)
<code>EFQ</code> | <code>bot -> A</code>
<code>DNE</code> | <code>~~A -> A</code> | <code>~</code> has a higher priority than any of <code>-></code>, <code>\|</code> and <code>&</code>

In order to pose an assumption, <code>Asm</code> is used as the reason.  Whereever the assumption is witten in the proof, either top, middle, or the bottom, it does not make any difference.
If a proof comes with assumptions, those assumptions are displayed in the left hand side of <code>⊢</code>

The inference rule <code>MP</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ B</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A -> B</code> and <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A</code>, two of which should be somewhere in previous proof steps.
Note that the formula <code>A</code> is distinct from any indexed ones <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
The inference rule <code>Gen</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ all x E(x)</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ E(x)</code> which should be a previous proof step, under the condition that <code>x</code> doesn't have a free occurrrence in any of the assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
The search for suitable proof steps for those inference rules is done automatically.
If one wants to explicitly specify the two proof steps, tagged by <code>#one</code> and <code>#two</code>, the arguments should be fed as <code>MP(#one, #two)</code>, which is order insensitive.

Example proofs are found in the <code>examples</code> directory.

<a name="todo"/>
## To do list
- Proof automation through the external prover Z3
- Epsilon equality axiom to implement
- Deduction theorem for proof transformation algorithm
- Further examples
