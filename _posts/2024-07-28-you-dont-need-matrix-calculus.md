---
title: "You Don't Need Matrix Calculus"
---

[Matrix calculus](https://en.wikipedia.org/wiki/Matrix_calculus) pops up on social media from time to time, primarily due to the increased popularity of machine learning. It lets you differentiate functions of vector or matrix variables even if you are not a fan of automatic differentiation. It involves all kinds of complex rules, depending on whether your vectors are row or column vectors, and it gets even worse for matrices. Let's not speak of tensors.

**You do not need matrix calculus**. When physists started working with tensors almost a century ago, they figured out the easy way to do this: instead of trying to come up with a system for tensor differentiation $\partial A / \partial B$, just write out the formulas for $A_{ijk}$ and $B_{ijk}$ and use ordinary differentiation.

The advantage is that this strategy always works, you only need to know how to do ordinary differentiation, and it's usually quicker, too. Matrix calculus only works for formulas in very specific form, and you need to memorize a bunch of new rules to apply it. Even then, it doesn't actually save much time, if any. *Just write out the indices!*

Consider the neuron activation function:

$$
  \mathsf{activation}(x) = \max(0, Ax + b)
$$

The max here is to be interpreted elementwise:

$$
  \mathsf{activation}(x)_i = \max(0, (Ax)_i + b_i) = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0\\
  (Ax)_i + b_i & \text{ otherwise}
  \end{cases}
$$

Let's just write out the matrix multiplication:

$$
  \mathsf{activation}(x)_i = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0\\
  \sum_j A_{ij}x_j + b_i & \text{ otherwise}
  \end{cases}
$$

Let's differentiate:

$$
  \mathsf{activation}(x)_i' = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0\\
  \sum_j (A_{ij}'x_j + A_{ij}x_j' + b_i') & \text{ otherwise}
  \end{cases}
$$

Note that we haven't said with respect to what we're differentiating, we just used the $y'$ notation. We have three possibilities:

1. Differentiate with respect to $x_k$
2. Differentiate with respect to $A_{kl}$
3. Differentiate with respect to $b_k$

To do so, we simply set the corresponding primed variable to $1$ and the other primed variables to $0$. For instance to differentiate with respect to $A_{kl}$ we set $A_{kl}' = 1$ and all the other $A_{ij}' = 0$ and $x_i'= 0$ and $b_i' = 0$:

$$
  \frac{\partial \mathsf{activation}(x)_i}{\partial A_{kl}} = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0\\
  x_l & \text{ otherwise}
  \end{cases}
$$

That's it. For the others:

$$
  \frac{\partial \mathsf{activation}(x)_i}{\partial x_{k}} = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0\\
  A_{ik} & \text{ otherwise}
  \end{cases}
$$

$$
  \frac{\partial \mathsf{activation}(x)_i}{\partial b_{k}} = \begin{cases}
  0 & \text{ if } (Ax)_i + b_i < 0 \\
  1 & \text{ if } i = k\\
  0 & \text{ otherwise}
  \end{cases}
$$

We got three for the price of one. Compare with the [matrix calculus derivation](https://explained.ai/matrix-calculus/). Can you decipher their final result for the derivative with respect to $w$? It's trickier than you think.