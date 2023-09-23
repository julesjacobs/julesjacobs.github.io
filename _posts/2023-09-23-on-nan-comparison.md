---
title: "On NaN comparison"
---

In most programming languages, the comparison operators (`<`, `<=`, `>`, `>=`, `==`) are defined to return `false` when one of the operands is `NaN`. In my opinion, this is a poor choice.

It breaks all kinds of fundamental properties that we expect from comparison operators. For example, we expect `x == x` to be `true` for all `x`, but this is not the case when `x` is `NaN`. We also expect `x < y` to be true if `y <= x` is false, and vice versa, but this is not the case when `x` or `y` is `NaN`.

## Some bad consequences

You can't test for `NaN` using `==`. This is only a minor problem and can be solved by using `isNaN` instead, which may be a good idea anyway if you can have multiple different kinds of `NaN` values (we'll get to that later). Still, it's confusing for beginners.

Sorting arrays containing `NaN` values is broken. If you sort an array containing `NaN` values, the result depends on the internals of the sorting algorithm, and even the non-`NaN` values can end up in strange positions, e.g. in Python:

```python
>>> sorted([6, 0, nan, 1, 2, 0, 9, 2])
[0, 0, 1, 2, 6, nan, 2, 9]
```

In Haskell, if you make a set of `NaN` values, then you can't test for membership or delete the `NaN` value from the set. Furthemore, you can have multiple duplicate `NaN` values in your set, even though the point of a set is to have unique elements.

`NaN` is not the only problem in this regard: `+0.0 == -0.0` is true, but `1.0 / (+0.0) == 1.0 / (-0.0)` is false. This creates a similar problem: if you have a set `{+0.0, -0.0}` then one of the zeroes gets removed, but you can't tell which one. Furthermore, if you map the function `f(x) = 1.0 / x` over such a set, then the set contains fewer elements than `{f(+0.0), f(-0.0)}`, which makes no sense.

## What should we do instead?

The IEEE 754 standard also defines a total order on floating point numbers. Programming languages should use this order for their comparison operators, and bitwise equality for their equality operator. This gets rid of all the problems mentioned above.
This is that total order:

<table border="0" style="border-collapse: collapse">
    <style type="text/css" scoped>
        td, th {
          font-family: monospace;
          padding: 3px 10px;
        }

        th {
          border-bottom: 1px solid #000;
          border-top: 1px solid #000;
          background-color: #AAA;
        }

        td {
          border-bottom: 1px solid #000;
        }
    </style>
    <thead>
        <tr>
            <th>Bit Pattern</th>
            <th>Meaning</th>
        </tr>
    </thead>
    <tbody>
          <tr>
            <td>1 11111111 1yyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Negative quiet NaN</td>
        </tr>
        <tr>
            <td>1 11111111 0yyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Negative signaling NaN</td>
        </tr>
        <tr>
            <td>1 11111111 00000000000000000000000</td>
            <td>-Infinity</td>
        </tr>
        <tr>
            <td>1 xxxxxxxx yyyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Negative number</td>
        </tr>
        <tr>
            <td>1 00000000 yyyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Negative denormal</td>
        </tr>
        <tr>
            <td>1 00000000 00000000000000000000000</td>
            <td>-0</td>
        </tr>
        <tr>
            <td>0 00000000 00000000000000000000000</td>
            <td>+0</td>
        </tr>
        <tr>
            <td>0 00000000 yyyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Positive denormal</td>
        </tr>
        <tr>
            <td>0 xxxxxxxx yyyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Positive number</td>
        </tr>
        <tr>
            <td>0 11111111 00000000000000000000000</td>
            <td>+Infinity</td>
        </tr>
        <tr>
            <td>0 11111111 0yyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Positive signaling NaN</td>
        </tr>
        <tr>
            <td>0 11111111 1yyyyyyyyyyyyyyyyyyyyyy</td>
            <td>Positive quiet NaN</td>
        </tr>
    </tbody>
</table>

<br>

[Here's how Rust implements this order](https://doc.rust-lang.org/src/core/num/f64.rs.html#1373).


## Are floats bad?

No! They get a bad rap, but floats are actually very good. Much of the criticism they receive is based on misunderstandings or poor priorities. Many of the attempts to replace them are mostly nonsense (but small floats for ML are good!).

It is important to remember that operations on floats generally return the *best possible result* given the constraints of the floating point format. For example, `1.0 / 3.0` returns the best possible approximation of `1/3` that can be represented as a float.

This means that operations on integers represented as floats are exact when the integers are not too large, because floats can represent integers exactly.

And sure, `3/10` can't be exactly represented as a float, just like `1/3` can't be exactly represented as a finite length decimal. That's just a conquence of floats being based on binary.

If you do need decimal precision up to 3 fractional digits, you can scale your floats by 1000, so that numbers up to 3 fractional digits become integers (12.345 → 12345). Then you retain the advantages of floats, but also get exact decimal precision up to 3 fractional decimal digits.

If you *really* want to represent many fractional *decimal* digits exactly, then you should use a decimal type, not a binary type. But in *almost all* cases, that's a bad decision. You should probably just use floats of a given precision. We only use decimal because evolution happened to give us 10 fingers. There's nothing special about it.