---
title: "On div and mod"
---

The % operator in most programming language computes the remainder after integer division. This works as expected when both operands are positive, but when one of the operands is negative we start to see differences between different programming languages:

<table style="text-align:center; border-collapse: collapse">
    <style type="text/css" scoped>
      td, th {
        padding: 3px 10px;
        border-bottom: 1px solid #000;
        font-family: monospace;
        width: 90px;
      }

      th {
        border: 1px solid #000;
      }
    </style>
    <thead>
        <tr style="background-color: #e0e0e0;">
            <th>Language</th>
            <th>8%3</th>
            <th>(-8)%3</th>
            <th>8%(-3)</th>
            <th>(-8)%(-3)</th>
        </tr>
    </thead>
    <tbody>
        <!-- Group 1: Light Blue -->
        <tr style="background-color: #b3e0ff;"><td>C</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <tr style="background-color: #b3e0ff;"><td>Rust</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <tr style="background-color: #b3e0ff;"><td>OCaml</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <tr style="background-color: #b3e0ff;"><td>Java</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <tr style="background-color: #b3e0ff;"><td>Pascal</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <tr style="background-color: #b3e0ff;"><td>Julia</td><td>2</td><td>-2</td><td>2</td><td>-2</td></tr>
        <!-- Group 2: Light Green -->
        <tr style="background-color: #b3ffb3;"><td>Python</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <tr style="background-color: #b3ffb3;"><td>Ruby</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <tr style="background-color: #b3ffb3;"><td>Racket</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <tr style="background-color: #b3ffb3;"><td>Mathematica</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <tr style="background-color: #b3ffb3;"><td>R</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <tr style="background-color: #b3ffb3;"><td>Haskell</td><td>2</td><td>1</td><td>-1</td><td>-2</td></tr>
        <!-- Group 3: Light Pink -->
        <tr style="background-color: #ffb3d1;"><td>Koka</td><td>2</td><td>1</td><td>2</td><td>1</td></tr>
    </tbody>
</table>

<br>
As you can see, all languages agree when both operands are positive, but there are three different ways to define the % operator when one of the operands is negative. The question I want to answer in this post is: **which of these three options is the best?**

To answer this question, we need to first understand the relationship between the div and mod operators.

## The relation between div and mod

The mod operator `x%n` is intimately related to the integer div operator `x/n`.
To distinguish this from mathematical division, I'll write this `x//n` like Python. In order for the choice of div-mod pair to make sense, we want these operators to satisfy the following equation:

    x%n = x - (x//n)*n

That is, we want the mod operator to actually give us the remainder after division.
This means that if we define integer division, then we have no choice for the mod operator because it is already determined by that equation.

## Option 1: C, Rust, OCaml, Java, Pascal, Julia

These languages define the div operator as *truncated* division, which means that the result is rounded toward zero:

$$x//n \triangleq{} \mathsf{trunc}\left(\frac{x}{n}\right)$$

We then define the mod operator in terms of the div operator:

$$x\%n = x - (x//n) \cdot n$$

## Option 2: Python, Ruby, Racket, Mathematica, R, Haskell

These languages define the div operator as *floored* division, which means that the result is rounded toward negative infinity:

$$x//n = \mathsf{floor}\left(\frac{x}{n}\right)$$

We then define the mod operator in terms of the div operator:

$$x\%n = x - (x//n) \cdot n$$

## Option 3: Koka

Koka takes a different approach, and instead defines the *mod* operator first.
Koka defines `x%n` as the *smallest non-negative number that makes `x - x%n` evenly divisible by `n`*:

$$x\%n = \mathsf{min} \{ y \in \mathbb{N} \mid x - y \text{ is divisible by } n \}$$

We can then define the div operator in terms of the mod operator:

$$x//n = \frac{x - x\%n}{n}$$

This works because `x - x%n` is always divisible by `n`, so the result is always an integer.

## Which is best?

Firstly, note that option 2 and option 3 agree about `x%n` whenever `n` is positive: they always give a result in the range `0..n-1` in that case.
Option 1, on the other hand, will give a negative result for `x%n` when `x` is negative, even when `n` is positive. This is bad, because it means that if you do something like `x % some_array.length`, you may get an index that is not even in bounds of the array. The second reason it's bad, is that `x%n` doesn't give you a unique representative of the equivalence class `x mod n`.

<span style="color: red; font-weight: bold">Option 1 is bad. If you're developing a new language, don't do this.</span>

Now, let's compare option 2 and option 3. The main difference is that option 2 gives you a more natural definition of the div operator, whereas option 3 gives you a more natural definition of the mod operator. The question is: which one is more useful?

This is less clear, and I'd argue that both options are acceptable. The advantage of option 3 is that it lets you more straightforwardly convert numbers to negative base. The same code that works for positive base also works for negative base.

On the other hand, option 2 is more natural for the div operator, and it is easy to get the Euclidean mod using the floored mod: `mod_euclid(x,n) = x % abs(n)`. I would argue that if your code is doing mod with negative divisors, then it is in fact clearer to have that explicit `abs` in your code as a signifier that something is going on.

<span style="color: green; font-weight: bold">Option 2 and 3 are both good. If you're developing a new language, choose one of these.</span>

They only differ for `x%n` when `n` is negative. That's not a common case, so it's not a big deal. I can see arguments in favor of both options. Which one would you choose? Let me know in the comments.

## Further reading

There are two great articles investigating this question, which I recommend reading:

1. [Division and Modulus for Computer Scientists](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf
) by Daan Leijen
2. [The Euclidean Definition of the Functions div and mod](https://dl.acm.org/doi/pdf/10.1145/128861.128862) by Raymond Boute
