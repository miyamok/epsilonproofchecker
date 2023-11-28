# Proof assistant for Hilbert's epsilon calculus and predicate calculus
_Epsilon_ is a proof assistant system for Hilbert's epsilon calculus and predicate calculus.  It supports Hilbert style proofs in epsilon calculus as well as in first order predicate calculus.
The proof scripting language is simple, and there are useful features such as proof transformation due to deduction theorem, which makes proof scripting in Hilbert style system easier, the lemma feature to use a previously proven lemma, and proof automation.  Automated theorem proving is due to an external tool Microsoft Z3 (https://github.com/Z3Prover/z3), and formulas in predicate logic and it's subsystems are supported.
##### Table of contents
- [Logic](#logic)
  - [Propositional calculus](#propositional-calculus)
  - [Elementary calculus](#elementary-calculus)
  - [Predicate calculus](#predicate-calculus)
  - [Epsilon calculus](#epsilon-calculus)
  - [Deduction theorem](#deduction-theorem)
- [Usage of the epsilon proof assistant](#usage-of-the-epsilon-proof-assistant)
  - [Syntax for proof scripts](#syntax-for-proof-scripts)
- [To do list](#to-do-list)
```
## ghc-9.2.8 used
% ghc Main
% ./Main examples/ex03_identity.proof
-- Correct proof of ⊢ A -> A
% cat examples/ex03_identity.proof 
A -> (A -> A) -> A by K
A -> A -> A by K
(A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A by S
(A -> A -> A) -> A -> A by MP
A -> A by MP
% ./Main examples/ex24_drinkers_paradox.proof
-- Correct proof of ⊢ ex x(P(x) -> all x P(x))
% ./Main examples/ex25_drinkers_paradox_eps.proof
-- Correct proof of ⊢ P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x))
% ./Main examples/ex05_wrong.proof
Error at line 1: A -> B by K
% cat examples/ex05_wrong.proof
A -> B by K
% ./Main examples/ex07_assumption.proof 
-- Correct proof of ⊢ A -> A
% cat examples/ex07_assumption.proof 
A by Asm
deduction-transformation
% z3 -version ## assume Microsoft's Z3 is installed
Z3 version 4.12.3 - 64 bit
% ./Main examples/ex18_inverse_AllShift_auto.proof
-- Correct proof of ⊢ (B -> all x P(x)) -> all y (B -> P(y))
% cat examples/ex18_inverse_AllShift_auto.proof
(B -> all x P(x)) -> all y (B -> P(y)) by Auto
```
## Logic
This section describes propositional calculus first, and then extends this calculus step-by-step to arrive at more powerful calculi such as predicate calculus and epsilon calculus.

Propositional calculus is a simple logic whose language consists of atomic propositions and logical connectives such as implication, negation, conjunction and disjunction which all appear even in our daily life.
Elementary calculus is an extension of propositional calculus.  It is obtained by extending propositional calculus by predicates and term constants.
Elementary calculus is a common basis of richer calculi such as predicate calculus and epsilon calculus.
Predicate calculus, first-order logic in other words, is elementary calculus with term variables, quantifiers, and additional logical reasoning methods concerning the quantifiers.
An example statement involving quantification is "there exists a white pigeon." where there is a quantification over pigeons.
Epsilon calculus is an extension of elementary calculus.  The language is enriched by the epsilon operator, and an additional reasoning method is available.
Epsilon operator is a term which forms a term from a formula.  For example, assume we have a formula claiming that "x is a white pegion," then epsilon operator allows to make a term meaning "an object which is a white pegion," namely, a white pegion.
See the difference between "there exists a white pigeon" and "an object which is a white pegion," where the former one is a claim of the existence of such a pigeon, that is definitely different from such a pigeon denoted by epsilon operator.
### Propositional calculus
For this moment, we restrict our base logic to the fragment of negation and implication.
Propositional formula <code>F</code> is defined as follows, where P<sub>0</sub> is ranging over propositional variables and <code>A</code> is an element of P<sub>0</sub>.
```
F ::= A | bot | F -> F
```
The arrow denotes logical implication, and <code>bot</code> is a special constant denoting falsum, which means the condtradiction.
The following formula means that if <code>A</code> then it contradicts.
```
A -> bot
```
In order words, it's not the case that <code>A</code> holds.
This formula, <code>A -> bot</code>, denotes the negation of <code>A</code> (namely, not <code>A</code>), and is abbreviated as
```
~A
```
Let <code>A</code>, <code>B</code>, and <code>C</code> be propositional variables in P<sub>0</sub>.
The following three expressions are examples of propositional formulas.
```
A
~A -> B
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
Implication in the right hand side has higher priority than the left, and we say that implication associates to the right.
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
If a proof concludes <code>A</code> from assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>, we write
<code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A</code>.
We often abbreviate the sequence of assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code> as <code>Γ</code>.
A reason is either an axiom, an inference rule, or a reference to an assumption.  We have the following axioms
```
A -> B -> A
(A -> B -> C) -> (A -> B) -> A -> C
bot -> A
~~A -> A
```
and one inference rule.
```
If Γ⊢A -> B and Γ⊢A then Γ⊢B
```
Each of the above has the names <code>K</code>, <code>S</code>, <code>EFQ</code>, <code>DNE</code>, and <code>MP</code>, respectively.
<code>K</code> and <code>S</code> are traditional names, and the rest stands for ex falso quodlibet, double negation elimitaion, and modus ponens.
Note that the axioms are actually axiom schemas, namely, those propositional variables in the axiom formulas may be replaced by arbitrary formulas.  In order words, those occurrences of <code>A</code>, <code>B</code>, <code>C</code> are metavariables and diffrent from propositional variables, and those metavariables will be instantiated by concrete formulas in actual use.
Here we give a proof of <code>A -> A</code>.
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
A disjunction formula <code>A | B</code> claims that <code>A</code> or <code>B</code> hold.

The way of reasoning with conjunction and disjunction is described in the next section, Syntax for proof scripts.
### Elementary calculus
Elementary calculus extends propositional calculus by terms and predicates for its language.
Let C<sub>0</sub> be a set of nullary constants, C<sub>1</sub> a set of unary (function) constants, and so, and let <code>c</code> and <code>f</code> be nullary and unary constants, respectively.  Also, let <code>Q</code> be an element of P<sub>1</sub>, a set of unary atomic predicates.  Let V be a set of variables, and assume <code>x</code> is a variable in V
Then the terms <code>t</code> and formulas <code>F</code> of elementary calculus is given as follows.
```
t ::= x | c | f(t)
F ::= A | bot | F -> F | F & F | (F | F) | Q(t)
```
Generally a formula <code>E</code> may contain a variable <code>x</code>.  In such a case, it is convenient to allow writing <code>E(x)</code> instead of <code>E</code>, and also allow writing <code>E(t)</code> for the formula obtained by replacing all occurrences of <code>x</code> in <code>E</code> by <code>t</code>.
Its axioms and inference rule are same as propositional calculus.
<a name="pred"/>
### Predicate calculus
Predicate caluclus is an extension of elementary calculus by quantifications.
The language is enriched by the existential quantifier and the universal quantifier.
The syntax is given as follows.
```
t ::= x | c | f(t)
F ::= A | bot | F -> F | F & F | (F | F) | Q(t) | ex x F | all x F
```
Assume <code>E(x)</code> is a formula containing a free variable x.  One interpretation of this formula is that it states some property of <code>x</code>.
By means of the quantifiers, it is possible to form the following quantified formulas
```
ex x E(x)
all x E(x)
```
which are commonly written as <code>∃x E(x)</code> and <code>∀x E(x)</code>, respectively.
They denote that there is some <code>x</code> such that <code>E(x)</code> holds, and that for any <code>x</code>, <code>E(x)</code> holds.

We have two kinds of variable occurrences due to the presence of the quantifiers.
Assume a formula <code>E(x)</code> is free from a quantifier and <code>x</code> has at least one occurrences in <code>E(x)</code>.
In the formula <code>all x E(x)</code>, all the occurrences of <code>x</code> is bounded, while all the occurrences of <code>x</code> in <code>E(x)</code> is free.
This variable binding mechanism is important to formulate the logic of predicate calculus, and the definition of free varialbles <code>FV</code> is given as follows.
```
FV(x) = {x}
FV(f(t)) = FV(t)
FV(bot) = {}
FV(P(t)) = FV(t)
FV(A -> B) = FV(A) ∪ FV(B)
FV(A & B) = FV(A) ∪ FV(B)
FV(A | B) = FV(A) ∪ FV(B)
FV(all x E(x)) = FV(E(x)) - {x}
FV(ex x E(x)) = FV(E(x)) - {x}
```
We allow to write <code>FV(A<sub>1</sub>, ..., A<sub>k</sub>)</code> to mean <code>FV(A<sub>1</sub>)∪...∪FV(A<sub>k</sub>)</code>. 
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
Epsilon operator is denoted by <code>eps</code> and forming a term taking a variable and a formula.
The language definition of epsilon calculus is as follows.
```
t ::= x | c | f(t) | eps x F
F ::= A | bot | F -> F | F & F | (F | F) | Q(t)
```
A term of the form <code>eps x E(x)</code> is called epsilon term.  Intuitive meaning of an epsilon term <code>eps x E(x)</code> is the term which satisfies the property of <code>x</code> denoted by <code>E(x)</code>.  Therefore, epsilon operator is often explained as a choice operator.
The definition of free variables is extended by the following clause to support epsilon terms.
```
FV(eps x E(x)) = FV(E(x)) - {x}
```
This intuition is formulated by the following critical axiom.
```
E(t) -> E(eps x E(x))
```
where <code>t</code> is an arbitrary term in epsilon calculus.
Epsilon operator is expressive enough to define the existential and universal quantifiers of predicate calculus, hence epsilon calculus is more expressive than predicate calculus, although the existential and universal quantifiers are missing in epsilon calculus.
Let <code>E(x)</code> be a formula, then the corresponding quantified formulas are defined as follows. 
```
ex x E(x) := E(eps x E(x))
all x E(x) := E(eps x ~E(x))
```
We are going to look at examples.
Assume the formula <code>A</code> does not contain a free variable <code>x</code>.
The following formula is known as independence of premise, whose proof is given as examples/ex22_independence_of_premise.proof .
```
(A -> ex x P(x)) -> ex x (A -> P(x))
```
Applying the definition of the existential quantifier by epsilon operator, the above formula goes to the following one.
```
(A -> P(eps x P(x))) -> A -> B(eps x(A -> P(x)))
```
A proof to this formula is given in examples/ex23_independence_of_premise_eps.proof .
```
(A -> P(eps x P(x))) -> A -> P(eps x (A -> P(x))) by C
```
Notice that this formula is an instance of the critical axiom.
Another example is a so-called Drinker's formula, which is often referred to as Drinker's paradox, and a proof is given as examples/ex24_drinkers_paradox.proof .
```
ex x(P(x) -> all x P(x))
```
The meaning of this formula is often explained through a story of a pub, that is, in a pub there is such a guy that if the guy is drinking then everybody in the pub is drinking.
This claim may sound a bit confusing, and this is the reason why this provable formula is called a paradox.  If there is a guy in the pub who is not drinking, you pick this guy, then the premise of the implication goes false, hence the whole formula is true.  Otherwise everybody is drinking, hence you can pick an arbitrary guy.  In case of a real pub, it is decidable whether there is a guy who is not drinking.  This formula is true even in case the matter is undecidable.
The epsilon version of the above formula is
```
P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x))
```
A proof is given in examples/ex25_drinkers_paradox_eps.proof
After proving the identity formula <code>P(eps x ~P(x)) -> P(eps x ~P(x))</code>, the rest of the proof goes as follows.
```
(P(eps x ~P(x)) -> P(eps x ~P(x))) -> P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by C
P(eps x(P(x) -> P(eps x ~P(x)))) -> P(eps x ~P(x)) by MP
```
### Deduction theorem
Deduction theorem claims that if <code>Γ, A ⊢ B</code> then <code>Γ ⊢ A -> B</code>.
An interesting aspect of the proof of this theorem is that it actually tells us how to get a proof of <code>Γ ⊢ A -> B</code> from a proof of <code>Γ, A ⊢ B</code>.
The epsilon proof assitant has a feature of proof transformation, which implements the algorithm in the proof of deduction theorem.

Deduction theorem holds for all the calculi supported by the proof assistant epsilon.
## Usage of the epsilon proof assistant
The Glasgow Haskell Compiler is prerequisite.
Get the source code and compile the code in the following way.
```
% cd epsilonproofcheker
% ghc Main
```
Then you can try examples in the <code>examples</code> directory.
```
% ./Main examples/ex22_independence_of_premise.proof
-- Correct proof of ⊢ (A -> ex x P(x)) -> ex x(A -> P(x))
% cat examples/ex22_independence_of_premise.proof
A -> ex x P(x) by Asm
~ex x(A -> P(x)) by Asm
A by Asm

...

~~ex x(A -> P(x)) -> ex x(A -> P(x)) by DNE
ex x(A -> P(x)) by MP
deduction-transformation
```
The oprion <code>-p</code> is to display the proof.
```
% ./Main -p examples/ex03_identity.proof
-- Correct proof of ⊢ A -> A
A -> (A -> A) -> A by K
A -> A -> A by K
(A -> (A -> A) -> A) -> (A -> A -> A) -> A -> A by S
(A -> A -> A) -> A -> A by MP
A -> A by MP
```
One example making use of the proof transformation is the proof of the excluded middle, which is available as <code>examples/ex16_excluded_middle.proof</code>.
```
A | ~A
```
First step is to prove that <code>A | ~A -> bot, A ⊢ bot</code> which is done in the lines 1 to 5 in <code>ex16_excluded_middle.proof</code>.
```
% cat examples/examples/ex16_excluded_middle.proof 
A | ~A -> bot by Asm
A by Asm
A -> A | ~A by DisjI1
A | ~A by MP
bot by MP
deduction-transformation
~A -> A | ~A by DisjI2
A | ~A by MP
bot by MP
deduction-transformation
~~(A | ~A) -> A | ~A by DNE
A | ~A by MP
```
By <code>deduction-transformation</code>, the first five lines, the proof of <code>A | ~A -> bot, A ⊢ bot</code>, is used to generate a new proof of <code>A | ~A -> bot ⊢ ~A</code>.
The proof scripts from the line 6 to 8 are added to the end of the new proof, and this establishes another proof concluding <code>A | ~A -> bot ⊢ bot</code> by the line 9.
Another deduction transformation is applied to generate a proof of <code>⊢ ~~(A | ~A)</code>, which yields the goal <code>⊢ A | ~A</code> by DNE and MP.

In lines after <code>deduction-transformation</code>, the original proof and tags there are not accessible.
The command line option <code>-p</code> may be helpful to get to know how the generated proof looks.

By issueing the following command, it shows the following output, which means that the proof of <code>A | ~A</code> has been checked.
```
% ./Main examples/ex16_excluded_middle.proof
-- Correct proof of ⊢ A | ~A
```
It is also possible to print out the final proof by the option <code>-p</code>.
```
% ./Main -p examples/ex16_excluded_middle.proof
```
The outcome consists of 64 lines, and would be hard without relying on the proof transformation, although there can be a clever idea for a shorter proof.

A proof script (it is exaxtly one file on the computer) may contain multiple proofs.
Completed proofs can be later used in other proofs.
By <code>end-proof</code>, the current proof is concluded and a new proof can start from the next line.
If you give also a name, <code>end-proof Lemma1</code> for example, this proof will be available in the future work via <code>Use</code> with the specified name, <code>by Use(Lemma1)</code> for example.  Use command makes the proven formula fit the target formula.  It means that a previously proven formula <code>A | ~A</code> is applicable to prove <code>ex x P(x) | ~ex x P(x)</code> via Use which finds and applies the suibstitution of <code>ex x P(x)</code> for <code>A</code>.

If the last step of the proof is <code>Asm</code>, the assumed formula is the conclusion of the proof.  If one wants to write a proof whose conclusion is directly from an assumption which is not the last <code>Asm</code>, one can use <code>Ref</code> to make a claim referring to an assumption.  An example is found in <code>examples/ex07_assumption.proof</code> which generates a proof of <code>⊢ A -> B -> A</code> from another proof of <code>A, B ⊢ A</code>.
```
% cat examples/ex07_assumption.proof 
A by Asm
B by Asm
A by Ref
deduction-transformation
deduction-transformation
```

On the other hand, it is also possible to make use of an external automated theorem prover.
For this moment, the epsilon proof assistant supports automation for predicate calculus and its subsystems due to Microsoft's Z3 (https://github.com/Z3Prover/z3).
Microsoft's Z3 is supposed to be installed and be avaialble from your command line via a command z3.
```
% z3 -version
Z3 version 4.12.3 - 64 bit
% ./Main -p examples/ex15_peirce_auto.proof 
-- Correct proof of ⊢ ((A -> B) -> A) -> A
((A -> B) -> A) -> A by Auto
```
Microsoft Z3 does not supply a syntactic proof of the claimed formula, but it just says "yes" or "no" as a result of determining the provability of the claimed formula.
There is no means for the proof assistant epsilon to verify the response from such an external prover, and the proof assistant epsilon simply accepts what the external prover said, in stead of performing a syntactic proof checking. 
It implies that the correctness of a proof involving Auto totally relies on the correctness of the external prover, and the epsiolon proof assistant does not guarantee anything.

The proof transformation feature does not maintain the tagged inference rules.  All tags are erased before transformation.

The next section provides sufficient information to start writing your own proofs.
### Syntax for proof scripts
The proof assistant epsilon processes a proof script which is stored as a file in the system.
The main content of a proof script is a proof, which is a list of proof steps, each of which consists of the following ingredients.
1. A formula to claim
2. A reason of claiming the formula
3. Optional tag for future reference to this proof step

Formula is what we saw in the previous section of this documentation.
A reason is either a name of an axiom, an assumption, or an inference rule which may come with an additional parameters.
A tag is a reference name, which is a string starting with <code>#</code>, given to the proof step, which can be used to point this proof step later on.

The follwoing variable names, constant names, and predicate names are available by default.

Kind | Default names
--- | ---
Variable | <code>x</code>, <code>y</code>, <code>z</code>, <code>u</code>, <code>v</code>
Nullary constant | <code>a</code>, <code>b</code>, <code>c</code>
Unary function constant | <code>f</code>, <code>g</code>
Binary function constant | <code>h</code>
Propositional variable | <code>A</code>, <code>B</code>, <code>C</code>
Unary predicate variable | <code>P</code>, <code>Q</code>
Binary predicate variable | <code>R</code>

Any of the above can be followed by an optional number as an index.  For example, <code>x</code>, <code>x1</code>, <code>x2</code> are all distinct variables.
Binary and unary constants and predicate variables should have a suitable number of arguments, which is a comma separated list with outer parentheses.
For example, <code>R(f(x), c)</code> is a well-formed formula, and on the other hand, <code>P</code> is not; <code>P</code> is a unary predicate variable and one argument is required, but it is missing.

Custom decalarations for variable names, constant names, and predicate names are available.
A declaration for variable names is done by a keyword <code>variables</code> followed by a space separated list of variable names, eg.
```
variables x y u v
```
For predicates and constants, one has to specify the arity in addition to the names.
For any natural number _n_, a declarations starts with _n_<code>ary-predicates</code> or _n_<code>ary-constants</code> and followed by a space separated list of names, eg.
```
0ary-predicates A B
1ary-predicates P Q
2ary-predicates R
0ary-constants c a
1ary-constants f g
```
All the declarations in a proof script must precede any proofs, namely, it is not allowed to put a declaration below the first proof step in a proof script.
A custom declaration makes the default names unavailable.  For example, assume one made a custom declaration for variables and didn't make any custom declarations for constants names nor predicate names.  In this case, the default variable names are gone, while the default constant names and predicate names are still there.

Command name | Example | Note
--- | --- | ---
<code>variables</code> | <code>variables x y</code> | Takes at least one variable name
_n_<code>ary-constants</code> | <code>0ary-constants c</code> | A natural number should be substituted for _n_
_n_<code>ary-predicates</code> | <code>2ary-predicates R S</code> | A natural number should be substituted for _n_
<code>deduction-translation</code> | | Applies the deduction translation to the<br />current proof
<code>end-proof</code> | <code>end-proof Lemma123</code> | Ends the current proof.<br />A lemma is saved, provided an argument given

Assume <code>E(x)</code> is a formula and X is some name of axiom or inference rule, the syntax of the proof step is given as follows
```
E(x) by X
```
and also one can give a tag to this proof step.
```
E(x) by X #myproofstep
```
The proof assistant epsilon supports the following axioms.

Axiom name | Scheme | Note
--- | --- | ---
<code>S</code> | <code>(A -> B -> C) -> (A -> B) -> A -> C</code> | <code>-></code> associates to the right
<code>K</code> | <code>A -> B -> A</code>
<code>C</code> | <code>E(t) -> E(eps x E(x))</code> | <code>t</code> is an arbitrary term in this whole table
<code>ConjI</code> | <code>A -> B -> A & B</code> | <code>&</code> associates to the left and has a higher<br /> priority than <code>-></code>
<code>ConjE1</code> | <code>A & B -> A</code>
<code>ConjE2</code> | <code>A & B -> B</code>
<code>DisjI1</code> | <code>A -> A \| B</code> | <code>\|</code> associates to the left and has a priority<br /> between <code>-></code> and <code>&</code>
<code>DisjI2</code> | <code>B -> A \| B</code>
<code>DisjE</code> | <code>A \| B -> (A -> C) -> (B -> C) -> C</code>
<code>ExI</code> | <code>E(t) -> ex x E(x)</code>
<code>ExE</code> | <code>all x(A(x) -> B) -> (ex y A(y) -> B)</code> | <code>x ∉ FV(B)</code> and (<code>x=y</code> or <code>y ∉ FV(A(x))</code>)
<code>AllE</code> | <code>all x E(x) -> E(t)</code>
<code>AllShift</code> | <code>all x(B -> A(x)) -> (B -> all y A(y))</code> | <code>x ∉ FV(B)</code> and (<code>x=y</code> or <code>y ∉ FV(A(x))</code>)
<code>EFQ</code> | <code>bot -> A</code>
<code>DNE</code> | <code>~~A -> A</code> | <code>~</code> has a higher priority than any of <code>-></code>,<br /> <code>\|</code> and <code>&</code>

In order to pose an assumption, <code>Asm</code> is used as the reason.  Whereever the assumption is witten in the proof, either top, middle, or the bottom, it does not make any difference.
If a proof comes with assumptions, those assumptions are displayed in the left hand side of <code>⊢</code>

The inference rule <code>MP</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ B</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A -> B</code> and <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ A</code>, two of which should be somewhere in previous proof steps.
Note that the formula <code>A</code> is distinct from any indexed ones <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
The inference rule <code>Gen</code> derives <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ all x E(x)</code> from <code>A<sub>1</sub>, ..., A<sub>k</sub> ⊢ E(x)</code> which should be a previous proof step, under the condition that <code>x</code> doesn't have a free occurrrence in any of the assumptions <code>A<sub>1</sub>, ..., A<sub>k</sub></code>.
The search for suitable proof steps for those inference rules is done automatically.
If one wants to explicitly specify the two proof steps, tagged by <code>#one</code> and <code>#two</code>, the arguments should be fed as <code>MP(#one, #two)</code>, which is order insensitive.

Inference rule name | Note
--- | ---
<code>MP</code> | Infers <code>Γ ⊢ B</code> from <code>Γ ⊢ A -> B</code> and <code>Γ ⊢ A</code>
<code>Gen</code> | Infers <code>Γ ⊢ all x A(x)</code> from <code>Γ ⊢ A(x)</code>, provided <code>x∉FV(Γ)</code>

Other than the axioms and inference rules, there are the following reasons which can be given after <code>by</code>.

Reason name | Example | Note
--- | --- | ---
<code>Asm</code> | <code>A -> A by Asm</code> | Makes an assumption.<br />Taken as a claim if a proof ends with it.
<code>Ref</code> | <code>A by Ref</code> | To refer to an assumption.
<code>Auto</code> | | Requires Microsoft's Z3
<code>Use</code> | <code>A -> A by Use(identity)</code> | A name of a suitable lemma required

Example proofs are found in the <code>examples</code> directory.

## To do list
- Packaging via cabal
- Implementing equality predicate and the epsilon equality axiom
- Supporting theorem prover E (https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html)
- Further examples
- Writing a brief history of Hilbert's logic
