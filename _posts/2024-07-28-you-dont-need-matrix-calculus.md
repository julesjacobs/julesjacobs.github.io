---
title: "You Don't Need Matrix Calculus"
---

[Matrix calculus](https://en.wikipedia.org/wiki/Matrix_calculus) pops up on social media from time to time, primarily due to the increased popularity of machine learning. It lets you differentiate functions of vector or matrix variables even if you are not a fan of automatic differentiation. It involves all kinds of complex rules, depending on whether your vectors are row or column vectors, and it gets even worse for matrices. Let's not speak of tensors.

**You do not need matrix calculus**. When physists started working with tensors almost a century ago, they figured out the easy way to do this: instead of trying to come up with a system for tensor differentiation $\partial A / \partial B$, just write out the formulas for $A_{ijk}$ and $B_{ijk}$ and use ordinary differentiation.

The advantage is that this strategy always works, and reliably produces the right answer. Matrix calculus only works for formulas in very specific form, and you need to memorize a bunch of new rules to apply it. Even then, it doesn't actually save much time, if any. *Just write out the indices!*