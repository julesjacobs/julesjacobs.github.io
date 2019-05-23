---
title: "Stronger unit propagation when solving CSPs with a SAT solver"
---

SAT solvers often beat CSP solvers at their own game, mainly because of clause learning, which enables further techniques like restarts and better variable selection heuristics. SAT problems have boolean variables whereas CSPs have variables with any finite domain. To encode a CSP variable x with finite domain `{1,2,3}` into SAT we introduce boolean variables `x1,x2,x3` which mean `x=1,x=2,x=3` respectively. I will write x=1 to denote the boolean variable `x1` and I will use `x!=1` to denote `!x1`. For the variable `x` we add a clause that ensures that at least one option must be set: `x=1 | x=2 | x=3` and we add clauses that ensure that no two options may be set at the same time: `x!=1 | x!=2`, and `x!=1 | x!=3`, and `x!=2 | x!=3`. For a CSP variable with domain of size N we get N boolean variables and 1 clause of size N and N(N-1)/2 clauses of size 2. We call these the variable clauses.

We also have to encode the CSP constraints into SAT clauses, but let's leave the details aside. I want to focus on the structure of a general SAT clause in the context of solving a CSP with a SAT solver. The clause might come from the encoding of CSP constraints, or it may be a learned clause. The point is that it involves only variables that come from translated CSP variables, which satisfy the variable clauses. This causes missed unit propagation.

Firstly, we have the equivalence `x!=2 <=> x=1 | x=3`, so we can always translate away negated variables.

Secondly, the order in a clause is irrelevant, so we can always group SAT variables by the CSP variable they come from, and instead of `x=1 | x=3` we use the shorthand `x∈{1,3}`.

The point is that any SAT clause in a CSP problem can be normalised to the form `x∈A | y∈B | ... | z∈C`.

When all but one literal in a clause has become false, unit propagation kicks in and sets the remaining literal to true. For a clause `x∈A | y∈B | z∈C` that means that when all possibilities `A` have been removed from the domain of `x`, and all possibilities `B` have been removed from the domain of `y`, and all but one possibility of `C` have been removed from the domain of `z`, *then* unit propagation sets `z` to the remaining possibility.

This is suboptimal. When all possibilities of `x` and `y` have been removed, the remaining clause is `z∈C`, so propagation could intersect the domain of `z` with `C`, even though in a SAT solver that wouldn't be a unit clause.

Therefore it might make sense to create a specialised SAT solver for CSPs, so that it may unit propagate a clause whenever the remaining literals belong to one CSP variable. The two-watched literal scheme of SAT solvers can readily incorporate this change: we maintain the invariant that the two watched literals are from different CSP variables. When we look for a new watch and can't find one satisfying the invariant, we unit propagate.