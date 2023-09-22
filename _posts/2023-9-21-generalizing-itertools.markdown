---
title: "Generalizing itertools"
---

Python's iterools module provides 4 useful combinatoric functions for generating `k`-length sequences from `n`-length sequences:

- `permutations(xs, k)`: All possible `k`-length sequences from `xs` without repeats
- `product(xs, k)`: Cartesian product of `xs` with itself `k` times
- `combinations(xs, k)`: All possible `k`-length sorted sequences from `xs` without repeats
- `combinations_with_replacement(xs, k)`: All possible `k`-length sorted sequences from `xs`

I think it is clearer to combine these into one function: `generate(xs, length, repeats=False, inorder=False)`.
Think of this function as generating all possible tuples by repeatedly selecting elements from `xs`.

- `length`: The length of the tuples to generate
- `repeats`: Whether to allow selecting the same element of `xs` multiple times for an output tuple
- `inorder`: Whether to select elements in `xs` from left-to-right or in any order

The itertools functions are then given as:

- `permutations(xs, k) = generate(xs, k, repeats=False, inorder=False)`
- `product(xs, k) = generate(xs, k, repeats=True, inorder=False)`
- `combinations(xs, k) = generate(xs, k, repeats=False, inorder=True)`
- `combinations_with_replacement(xs, k) = generate(xs, k, repeats=True, inorder=True)`

## The twelvefold way

We can generalize this further to the [Twelvefold way](https://en.wikipedia.org/wiki/Twelvefold_way) by adding two more parameters:

- `missing`: Whether elements from `xs` are allowed to be missing from an output tuple
- `skip`: Whether we are allowed to skip over elements of the input list while generating an output tuple

Note that `repeats` and `missing` together control how often each source element will be selected:

- `repeats=True, missing=True`: Each element can be selected any number of times
- `repeats=True, missing=False`: Each element must be selected at least once
- `repeats=False, missing=True`: Each element can be selected at most once
- `repeats=False, missing=False`: Each element must be selected exactly once

The `skip` parameter controls whether we can skip over elements of the input list while generating the output tuple.
If `skip=False`, then every time we select a new element, we must either select the next element we haven't yet picked, or any of the elements we have previously picked.

The `skip` and `inorder` parameters are intimately related: `inorder` determines whether we generate only tuples that are lexicographically minimal with respect to permutations of the output, and `skip` determines whether we generate only tuples that are lexicographically minimal with respect to permutations of the input. For instance, if the input is `xs=[0,1,2]` then the output `(0,2,2)` is not minimal with respect to permutations of the input, because we have skipped over element `1` (i.e, because `(0,1,1)` is lexicographically smaller). On the other hand, `(0,2,0)` is not minimal with respect to permutations of the output, because the tuple is not sorted (i.e., because `(0,0,2)` is lexicographically smaller).

To visualize this, consider that we generate an output tuple by having a pointer into `xs`. The `inorder` parameter determines whether the pointer is allowed to move backward, and the `skip` parameter determines whether the pointer is allowed to move forward over elements that have not yet been selected.

Whether these generalizations are practically useful is debatable, but I think it's nice to have a single function that can generate all of these different types of tuples corresponding to the standard combinatoric classification of the twelvefold way.

## Further generalization

There are many more generalizations we could make. For instance, instead of specifying whether elements can be used at most once or a least once, we could specify a list of sets `counts` such that the set `counts[i]` specifies the allowed number of times that element `xs[i]` may be picked.

Similarly, we could generalize `inorder` and `skip` to other types of constraints on the movement of the pointer into `xs`.

However, at this point it becomes clear that we are just generating all possible tuples that satisfy some arbitrary constraint. This is a very general problem. One way to generalize it is to just generate all tuples and filter out the ones that satisfy some criterion. Unfortunately, this can be extremely slow. For instance, if we generate permutations this way, then we first generate all $$n^n$$ tuples, and then we filter out the $$n!$$ permutations. This is a huge waste of time.

A better way to generalize this problem is to use a higher-order function. One option is the following:

```python
generate(f : list[T] → (bool, list[T])) → list[list[T]]
```

This function takes a predicate `f(xs)` that takes a list of elements and returns a pair `(b, ys)` where `b` is a boolean indicating whether the list `xs` satisfies the constraint and should be included in the output, and `ys` is a list of all possible extensions of `xs` that will potentially satisfy the constraint. The function `generate` then returns a list of all lists that satisfy the constraint.

The generate function starts with the empty list `[]`. It calls `f` on the empty list to determine whether it should be included in the output, and to get a list of all possible extensions of the empty list. It then calls `f` on each of these extensions to determine whether they should be included in the output, and to get a list of all possible extensions of each of these extensions. It continues this process until it has generated all lists that satisfy the constraint.

This is a very general way to generate all lists that satisfy some constraint. For instance, we can generate all `k`-permutations of a list `xs` by using the predicate `f(ys) = (len(xs) == k, [xs + [x] for x in xs if x not in xs])`.

A way to further generalize is to allow `f` to use its own data type for its internal state, similar to `unfold` in Haskell:

```python
generate[S,A](init : S, f : S → (list[A], list[S])) : list[A]
```

This function takes an initial state `init` and a function `f` that takes a state `s` and returns a pair `(xs, ss)` where `xs` is a list of elements to be included in the output, and `ss` is a list of all successor states to explore. The function `generate` then returns a list of all elements that can be reached from `init` by repeatedly applying `f`.

I'm sure that an experienced Haskell programmer could write this as a one-liner using a monadic function from Haskell's standard library.

A way to further generalize this is to go all the way to constraint programming. In constraint programming, we _can_ specify a constraint, and have the constraint solver be responsible for generating all solutions that satisfy the constraint. This is much more efficient than generating all possible solutions and then filtering out the ones that satisfy the constraint, but it requires the constraint to be formulated in a way that the constraint solver can understand.
