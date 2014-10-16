---
layout: post
title:  "Newton, The Ultimate: One Weird Trick To Make You A Mathematical Superhero, part 1"
date:   2014-10-16 17:33:40
categories: math, programming
---

Ever wanted to be a mathematical superhero? Here's your chance! In this post I'm going to give you a one line algorithm for solving any equation and solving any optimization problem. Here it comes:

    iterate x <- x - f(x)/f'(x)
    
This is [Newton's algorithm](http://en.wikipedia.org/wiki/Newton's_method), and it will find you an `x` such that `f(x) = 0`. Lets try it out.

## Linear equations ##

We want to solve `3*x - 5 = 0` so we take `f(x) = 3*x - 5`. The derivative of f is `f'(x) = 3`, so Newton's algorithm becomes:

    iterate x <- x - (3*x - 5)/3
    
We simplify this to:
    
    iterate x <- 5/3
    
This is not a terribly exciting iteration, but it did give us the right answer: `f(5/3) = 0`. The reason that Newton's method solves linear equations in one step is that Newton's method works by making a linear approximation to your function, and then solving the equation for the linear approximation. So if your function was linear to begin with, it's not an approximation at all, and it will give you the right answer in one step. Here's an excellent animation from Wikipedia that shows this in action for a non linear function:

![Newton's algorithm animation](http://upload.wikimedia.org/wikipedia/commons/thumb/e/e0/NewtonIteration_Ani.gif/300px-NewtonIteration_Ani.gif)

## Function inversion ##

Suppose we have some function `g` and a number `a` and we want to solve `g(x) = a`. We rewrite this as `g(x) - a = 0` so we get `f(x) = g(x) - a` and apply Newton's algorithm. The derivative `f'(x) = g'(x)`. The algorithm becomes:

    iterate x <- x - (g(x) - a) / g'(x)
    
This can compute the inverse of any function!

### Square roots ###

We want to invert the function `g(x) = x^2`, in other words we want to compute square roots. Since `g'(x) = 2*x` we get:

    iterate x <- x - (x^2 - a)/(2*x)
    
We can further simplify this if we want:

    iterate x <- (x + a/x)/2
    
Now we have a real iteration that will take more than one step to converge, but what `x` do we start with? You want to start with a number that's reasonably close to the answer. How many iterations? That doesn't really matter! Newton's method is so fast, it usually converges in a handful of iterations. Let's use this to solve the equation `x^2 = 2` in Python:

{% highlight python %}
a = 2     # equation we want to solve is x^2 = a
x = 10    # terrible initial guess
for i in range(0,10):
   x = (x + a/x)/2
   print x
{% endhighlight %}

This gives us the following sequence:

    5.1
    2.74607843137
    1.73719487438
    1.44423809487
    1.41452565515
    1.4142135968
    1.41421356237
    1.41421356237
    
Notice how fast that converged to `sqrt(2)`? This is a general property of Newton's method: on each iteration we get about twice as many digits of accuracy.

### Division ###

Now that we've used Newton's algorithm to compute square roots, let's try something else. Can we get Newton's algorithm to compute division `1/a`? (then we can compute arbitrary division with `b/a = b * 1/a`) Lets make a function out of that: g(x) = 1/x. We are going to apply Newton's method to compute the inverse of `g`. "But the inverse of `g` is `g`", you say, "How could that possible help us?". Lets just march on anyway: `g'(x) = -1/x^2`, so the algorithm becomes:

    iterate x <- x - (1/x - a)/(-1/x^2)
    
So how did that help us? To compute division we know have to compute *three* divisions *each iteration*! We can simplify this:

    iterate x <- x*(2 - a*x)
    
Whoa! Where did the divisions go? Lets try it out:

{% highlight python %}
a = 7.0     # we compute 1/a
x = 0.1     # initial guess
for i in range(0,10):
    x = x*(2 - a*x)
    print x
{% endhighlight %}

This gives:

    0.13
    0.1417
    0.14284777
    0.142857142242
    0.142857142857
    0.142857142857

Great, we've computed `1/7`. This is actually the method that some CPUs use to divide! This brings us to one of the limits of our mathematical superpowers. What if we had used `0.5` as our initial guess instead of `0.1`. Lets try it:

    -0.75
    -5.4375
    -217.83984375
    -332615.062363
    -7.74430123204e+11
    -4.19819411008e+24
    -1.23373836501e+50
    -1.06547724731e+101
    -7.94669235181e+202
    -inf
    
Hmm, that doesn't look too good. If our initial guess is too far off, then sometimes Newton's method can diverge (this also depends on the equation we're trying to solve).

### Complicated equations ###

What about an equation like [sin(x) + log(x) = 2](http://www.wolframalpha.com/input/?i=sin%28x%29+%2B+log%28x%29+)? We get Newton's algorithm:

    iterate x <- x = x - (sin(x) + log(x) - 2)/(cos(x) + 1/x)
    
And the output:

    9.67332523525
    9.70032160401
    9.70042510551
    9.70042510714
    9.70042510714
    
And sure enough, if we compute `sin(9.70042510714) + log(9.70042510714)` we get a number that's extremely close: 2.0000000000000004.

Stay tuned for the next episode(s), where we use Newton's method to find the maximum of a function, to solve whole systems of equations with multiple variables, to solve differential equations, to do variational optimization problems, to solve optimization problems with equality and inequality constraints, such as linear programming.