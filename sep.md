I'll write down some thoughts on what we talked about, namely: how can we make the development of verified + performant code less costly?

# Existing approaches and their trade-offs

## Approach 1: Separation logic verification

The most prominent approach to verifying 'real' code is separation logic (e.g., Iris and Viper).
Separation logic is quite powerful (can verify imperative and parallel code), but in practice this amounts to:

1. Building a purely functional model of your code (i.e., writing a second copy of your codebase)
2. Proving separation logic specs that relate the real code to the purely functional model
3. Proving correctness properties of the functional model
4. Using the specs of (2) to transport the correctness properties to the real code

This is not an issue and can often be avoided in simple examples, but when your code consists of real abstractions with user defined data structures that must be reasoned about, you pretty much have to follow the (standard) recipe above.

Some challenges of this approach are:

- Programmers need to be triple experts (real code + separation logic + functional model)
- A lot of duplicate work is being done, which involves careful planning and makes the code hard to change
- Hard to express certain properties, e.g., need relational Hoare logic to talk about equivalence of programs

## Approach 2: Purely functional programming directly in a proof assistant

CompCert is the prime example of this approach: write your code in the purely functional core of a proof assistant.

This approach addresses the main challenges of Approach 1:

- Only one copy of your code
- Language in which you write specs is the same as the one you program in
- Specs can directly talk about expressions and values
- As a special case of the point above, specs can directly talk about equivalence simply as `a = b`.

Some challenges of this approach are:

- Hard to get good performance
- Hard to write even normal functional code if the core is a total (terminating) language
- Absence of imperative constructs. These can be quite convenient and are arguably the right language for many algorithms

## Variations

I view the two approaches above as the two fundamental approaches, but nowadays there are many variants.
For instance, approach 2 can be done in a dependently typed language or a higher order logic.
In a dependently typed language you have further design choices (e.g., the Coq/Lean approach of stating separate lemmas, versus the Agda approach of encoding correctness in the types of the code itself).
There are other variants such as refinement types (e.g., Liquid Haskell), or hybrids such as Dafny.

For separation logic verification there are axes of variation as well, such as the more automated tools (Viper) and interactive tools (Iris).

The automated vs interactive distinction is cross-cutting and is also relevant for Approach 1.
I generally favour the interactive approach, as this seems to scale much better to larger real world code, both intuitively and in observable practice (e.g., CompCert, CakeML, seL4).
To me, a good way to do automation is as a tactic to discharge proof goals in interactive proofs (potentially invoked automatically for simple proof obligations).
This combines the advantages of foundational and flexible arbitrary mathematical reasoning with convenient automated proof wherever it works, while avoiding most of the pitfalls of trying to use an automated prover for goals for which it is not very suitable.

## Approach 3: "Non-mutably-aliased programming by type checking"

This approach consists of using a language like Rust, where high performance (imperative) code is supported, but separation logic is nevertheless not needed to reason about code, because the language ensures no aliasing by design. Prusti and Aeneas are examples of tools that take advantage. In effect, a program in a certain fragment of Rust corresponds directly to a purely functional program, so this approach can be seen as relaxing the "purely functional" restriction to "purely non-mutably-aliased".

This approach adresses the performance issues of Approach 2, while still not requiring separation logic as in Approach 1.

However, certain new challenges appear:

- Type system can be heavyweight, and gets in the way even in code that isn't performance critical => quite different in feel from lightweight Python/OCaml
- Temptation to "just .clone()" on borrow check error => performance needs careful management and design
- Purely functional programming is painful and slow when done naively due to the point above
- Specs and propositions can to some extent be written in the same programming language itself, but there are many limitations (not at all as fluent as in HOL or dependent type theory)
- Doesn't really make sense to have borrow checking inside spec code

# Approach 4: "Non-mutably-aliased programming by design"

This is a variation on Approach 3, where instead of using an ownership type system and borrow checker, we just bake this into the language semantics.
One dead simple (almost braindead) way to achieve this is to insert implicit .clone()'s on variables uses (other than on the left hand side of an assignment).

For example:

    x = [1,2,3]
    y = x         // traditionally creates alias, here implicitly copies x
    x[2] = 4      // now x=[1,2,4], y=[1,2,3]
    y[2] = 5      // now x=[1,2,4], y=[1,2,5]

However, if we try to define abstractions:

    def assign(x, i, v):
        x[i] = v

    x = [1,2,3]
    y = x
    assign(x, 2, 4)      // oops, we pass a copy of x into assign, so it didn't modify x
    assign(y, 2, 5)      // same here

We'd need an additional `mut` feature:

    def assign(mut x, i, v):
        x[i] = v

    x = [1,2,3]
    y = x
    assign(mut x, 2, 4)      // actually modifies x now
    assign(mut y, 2, 5)      // same here

Conceptually, `mut` semantics would be defined as a desugaring to a pure function like this:

    def assign(x, i, v):
        x[i] = v
        return x

    x = [1,2,3]
    y = x
    x = assign(x, 2, 4)
    y = assign(y, 2, 5)

Of course, in actuality you wouldn't want to do this desugaring; an implementation should actually suppress the implicit copy on `mut` parameters whenever possible.
Finally, you'd also want to be able to dig into data structures:

   xs = [[1,2,3], [4,5,6]]
   assign(mut xs[0], 2, 4)
   // now xs = [[1,2,4], [4,5,6]]

Note that the invariant is maintained (as in Rust) that the inner arrays are not aliased, e.g.,

   x = [1,2,3]
   xs = [x, x]         // copies (conceptually)
   xs[0][2] = 4
   // now xs = [[1,2,4], [4,5,6]]

Now you've got a simple language where you can do your imperative programming, and feels very lightweight like (statically typed) Python/OCaml, and can safely interoperate with Rust.
Because it's so close to functional programming, you could use this as the core of a higher order logic or even dependently typed language.
Specs can talk directly about values, without separation logic, and specs can be written in the language itself.

The main issue is that those implicit copies could lead to performance cliffs in innocent looking code.
This can be addressed in several ways: 
(1) Static analysis that determines when copies can be safely statically elided (e.g., "borrow checker as performance optimization")
(2) Dynamic language runtime that determines when copies can be safely dynamically elided (e.g., copy-on-write)
(3) Profiling tools that show where copies still happen

In general, I believe something like this allows you to write code with performance somewhere between Java and Rust, and possibly also better than naively written Rust:
- Better than Java because non-aliased language semantics enable better data representations. Java implementations must have pointers everywhere, because aliasing semantics must be respected. For instance, if you have an array of (mutable) pairs, JVM must have a pointer indirection on each pair, in order to maintain correct semantics when multiple array elements are aliased to the same pair. Pointer indirections are really slow these days. Compilers are really good at local rewriting optimization, but data representation transformations are global changes and compilers are really bad at it.
- Naively written code would potentially be better than naively written Rust, because there is a temptation to "just .clone() on borrow check error", (or in C++: "better copy just to be safe") which is potentially worse than (1) and (2) above [Google Chrome famously made 25000 string copies on each keystroke typed in the URL bar]

## Steps toward trying out this experiment

Trying out something along these lines could involve these steps:

1. Implement simplest possible prototype
2. Add higher-order logic on top
3. Prove this logic sound (e.g., in Coq/Lean)
4. Simple but OK compilation strategy that lets you write some reasonably performing code

Afterwards, one could further explore this language design space (analogue to FnMut-closures, dependent types, etc.) and implementation strategies ((1), (2), (3) above, integrate something like Rupicola for hot loops, etc.), alternative verification approaches (e.g., by translation to Coq/Lean), Rust interop (& verifying code that calls into verified Rust), integrate separation logic verification of very low level code with end-to-end correctness theorem, and so on.

## Opportunities are risks

Personally I think an approach along the lines of what I sketched above could be a promising point in the design space wrt simplicity, ease of use, performance, and ease of human (local) reasoning about code, as well as formal verification. Chances of this approach taking the world by storm are, obviously, low, but nonzero. On the other hand, I think the technical feasibility of producing a working prototype with interesting properties is quite reasonable.


# Summary

Problem 1: Rust is hard to learn and use due to its complex type system. We need high-level counterpart for non-systems software: "What is to Rust as Python is to C?".

Problem 2: Formal verification of code is hard due to aliasing (=> separation logic). Formal verification by "programming in mathematics" a la CompCert works well, but programming with pure mathematical functions is difficult for programmers and leads to slow code.

Goal: solve Problem 1 and Problem 2 simulatneously and with the same solution. Develop language that is easy to use, performant, and a basis for formal verification, without a complex type system.

* Practical, "Pythonic" programming language that simultaneously serves as a foundation for formal proof.
* Copy-on-alias semantics to solve mathematical inconsistency with imperative constructs.
* Enable efficient data representations, compiler optimizations.
* Safe and seamless Rust interoperability (conventional high level languages don't uphold critical Rust "aliasing xor mutability" invariant).
* Borrow checker becomes a compiler optimization and linter.

Helpful skills: Strong mathematical background, interest in type theory or logic, language design taste, compiler development.

Related: Lean, F*, Coq, Rust, Swift, Hylo, Aeneas, Prusti, Creusot, ...