---
layout: post
title:  "Simpler and faster Levenshtein automata"
date:   2016-08-26 00:30:00
categories: 
---

Some time ago I wrote a blog post [Levenshtein automata can be simple and fast](http://julesjacobs.github.io/2015/06/17/disqus-levenshtein-simple-and-fast.html) as an alternative to the rather more complex paper [Fast String Correction with Levenshtein-Automata](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.16.652), and then Paul Masurel wrote a blog post [Of Levenshtein Automata implementations](http://fulmicoton.com/posts/levenshtein) with a very good explanation of the algorithm in the original paper. The algorithm in the paper is table driven, and in thist post we will adapt the algorithm in my previous post to get a table driven automaton as well. In addition we'll get a simplification of the algorithm by using a short dense vector instead of a sparse vector, which is independent on whether we make it table driven or not, so let's start with that.

As explained in the previous post, if we are looking up to Levenshtein distance D, then only the diagonal band of size 2D+1 of the Levenshtein matrix matters. All entries outside of that band will be more than distance D anyway. This means that instead of keeping a full row as the state of the automaton, we only need 2D+1 entries of it. At first I thought the edge conditions would make it more complicated than a sparse vector, but it turns out that if we keep two additional entries on each side of the vector we can avoid all special handling for the first and last entries. The start state of the automaton is the relevant piece of the first row of the Levenshtein matrix.

{% highlight python %}
start = [abs(n) for n in range(-D-1,D+2)]
{% endhighlight %}

In order to make it table driven later, we're going to factor out the character comparisons into a separate function cmpvector(string, c, i), which takes a query string, a character to compare with, and an index. It returns a bitvector like 11001 that indicates where query string has character c near index i, which are the comparisons we need to compute the next row in the Levenshtein matrix.

{% highlight python %}
def cmpvector(string, c, i):
    return sum((j >= 0 and (j >= len(string) or string[j] != c)) << j+D-i for j in range(i-D,i+D+1))
{% endhighlight %}

Now we can compute the next state of the automaton given a current state and a comparison vector by using the usual Levenshtein algorithm and just not computing the parts of the row that we don't need.

{% highlight python %}
def step(state, cv):
    new_state = state[:]
    for i in range(1,len(state)-1):
        new_state[i] = min(new_state[i-1]+1, state[i] + (cv>>(i-1) & 1), state[i+1]+1, D+1)
    return new_state
{% endhighlight %}

This is where the keeping the extra two entries on both sides come in handy; otherwise we'd have needed to special case the computation for the first and last index. We can step through the automaton with `step(state, cmpvector(query, c, i))`. To determine whether the search in a trie can be pruned or whether the automaton can still match given future input, we use:

{% highlight python %}
def can_match(state): return min(state) <= D
{% endhighlight %}

Now we have a simpler non-table-driven automaton. To make it table driven we could memoize step, but that uses a dictionary under the hood. We should use an array to make the algorithm amenable to a fast implementation in a language like C. Since there are finitely many states for fixed distance D we give each state an integer id. We then turn a call `step(state, cv)` into an array lookup `step_table[state_id][cv]`, and `can_match(state)` into `can_match_table[state_id]` and similarly for `is_match`. This is also why we used a bitvector for the comparison vector: being a simple int, it can be used for indexing into an array. Building the tables is done by recursively exploring the states:

{% highlight python %}
step_table = []
can_match_table = []
done = {}

def explore(state):
    s = tuple(state)
    if s not in done:
        done[s] = len(step_table)
        can_match_table.append(can_match(state))
        step_table.append([])
        step_table[done[s]] = [explore(step(state,cv)) for cv in range(0, 1 << (2*D+1))]
    return done[s]

explore(start)
{% endhighlight %}

For large D this is not advisable, as the number of states grows rapidly, but for D=1 and D=2 there are just 9 and 51 states.