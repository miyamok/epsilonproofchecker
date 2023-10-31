# epsilonproofchecker
```
% ghc Main
% ./Main ex04_identity.proof
(A -> A)
is proved
% ./Main ex05_drinkers_paradox.proof
(P(eps x((P(x) -> P(eps x(~P(x)))))) -> P(eps x(~P(x))))
is proved
% ./Main ex06_wrong.proof
Not a proof of
(A -> B)
% 
```
