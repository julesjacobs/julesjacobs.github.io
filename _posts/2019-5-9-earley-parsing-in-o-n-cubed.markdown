---
title: "Earley parsing in cubic time"
---

Wait, isn't the point of Earley parsing that it's O(n<sup>3</sup>)? Actually, no, for a grammar of size G, Earley parsing an input of length n takes O(Gn<sup>3</sup>). How could you even possibly parse in time independent of the size of the grammar? Consider regular expressions: you can run them in O(Gn) with an NFA, but if you precompute a DFA you can run them in O(n), independent of the size of the original regular expression. Is such a thing possible for context free grammars? It turns out that yes, this is possible.

Usually Earley parsing is done one Earley item at a time, but the paper [Practical Earley Parsing](https://pdfs.semanticscholar.org/5b27/7a3f9a9f5250939f334e282d1393971722a9.pdf) explains how to use LR(0) states as Earley items. This doesn't yet make it O(n<sup>3</sup>), but it's a step in the right direction. We need a way to merge LR(0) states with the same index (i,j), and a way to run the completer for many completed items at the same time. Then we'll need to carefully analyse how the worklist in Earley's algorithm adds new Earley items, and perform those updates with sets at a time in such a way that we don't need a worklist any more. Here's what that looks like in Python:

{% highlight python %}
grammar = {"S":{"S+S","S*S","(S)","n","T"}, "T":{"n","T+T","S+S+S"}}
input = "n+n+(n+n)*n"

def fix(S,f): return S if S==f(S) else fix(f(S),f)

def completerC(I,C): return set(s for s,p in I if p[0] in C and len(p)==1)
def completerI(I,C): return set((s,p[1:]) for s,p in I if p[0] in C and len(p)>1)
def completerC_closure(I,C): return fix(C, lambda c: c | completerC(I,c))
def predictor(I): return fix(set(), lambda i: set((p1[0], p2) for c,p1 in i|I for p2 in grammar.get(p1[0],[])))

C,I = defaultdict(set),defaultdict(set)
I[0,0] = predictor({("","S")})

for k in range(1,len(input)+1):
    C[k-1,k] = {input[k-1]}
    for i in reversed(range(0,k)):
        for j in range(i+1,k): C[i,k] |= completerC(I[i,j], C[j,k])
        C[i,k] = completerC_closure(I[i,i], C[i,k])
        for j in range(i,k): I[i,k] |= completerI(I[i,j], C[j,k])
    for j in range(k): I[k,k] |= predictor(I[j,k])

print("S" in C[0,len(input)])
{% endhighlight %}

(sorry, I had to codegolf that to make it fit in a slide -- how those functions work is too much work to explain anyway)

The functions completerC, completerI, completerC_closure, and predictor work on LR(0) states I and sets of completed items C. You could hashcons & memoize them to build parse tables lazily, or you can precompute those parse tables. In either case, they'd run in O(1) eventually. The main loop of the algorithm is just a bunch of nested loops. The highest nesting level is 3, so it runs in O(n<sup>3</sup>) if those functions are memoized to run in O(1).

You can see the algorithm in action on four examples [here](/code/cubedearley/Sa.html), [here](/code/cubedearley/aS.html), [here](/code/cubedearley/SS.html), and [here](/code/cubedearley/arith.html). Use the left and right arrow keys on your keyboard to step forward and backward. Enjoy!z