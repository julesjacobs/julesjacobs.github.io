I'll sketch one possible answer to the following question: how can we make the development of verified + performant code less costly?

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

## Approach 2: Purely functional programming directly in a proof assistant

CompCert is the prime example of this approach: write your code in the purely functional core of a proof assistant.
Some challenges of this approach are:

- Hard to get good performance
- Hard to write even normal functional code if the core is a total (terminating) language
- Imperative constructs can be quite convenient and often the right language for expressing many algorithms

## Other appraoches

I view the two approaches above as the two fundamental approaches, but nowadays there are many variants.
For instance, approach 2 can be done in a dependently typed language or a higher order logic.
In a dependently typed language you have design choices (e.g., the Coq/Lean approach of stating separate lemmas, versus the Agda approach of encoding correctness in the types of the code itself).
There are other variants such as refinement types (e.g., Liquid Haskell), or hybrids such as Dafny.

For separation logic verification there are many variants as well, such as the more automated tools (Viper) and interactive tools (Iris).

The automated vs interactive distinction is cross-cutting and also appears in Approach 1.
I generally favour the interactive approach, as this seems to scale much better to larger real world examples, both intuitively and in observable practice (e.g., CompCert, CakeML, seL4).
To me, a good way to add automation is as a tactic to discharge proof goals in interactive proofs (potentially invoked automatically for simple proof obligations).
This combines the advantages of foundational and flexible arbitrary mathematical reasoning with convenient automated proof wherever it works, while avoiding most of the pitfalls of trying to use an automated prover for goals for which it is not very suitable.

