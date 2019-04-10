---
title: "Disambiguation of context free grammars"
---

A naive context free grammar for arithmetic expressions is ambiguous:

{% highlight fsharp %}
E  ->  E '+' E  |  E '*' E  |  'n'
{% endhighlight %}

The input `n+n+n` can be parsed as `(n+n)+n` or `n+(n+n)`, and the input `n+n*n` can be parsed as `(n+n)*n` or `n+(n*n)`. A parser for general context free grammars can produce a parse forest that contains all the ways of parsing an input string. However, in practice we only want one parse tree, selected according to precedence and associativity rules. Parser generators support disambiguation rules to specify which parse tree you want by filtering out the trees that you don't want. This becomes more complicated when prefix operators and if-then/if-then-else is involved. You end up filtering out all parse trees if the filtering rules are too strict, and you still end up with multiple parse trees if they are too loose. By carefully crafting the filtering mechanism you can make sure that you end up with one parse tree, but you may have to look arbitrarily deeply into a parse tree to figure out whether it should be filtered out. The article [Towards Zero-Overhead Disambiguation of Deep Priority Conflicts
](https://researchr.org/publication/AmorimSV18) by Luís Eduardo de Souza Amorim, Michael J. Steindorfer and Eelco Visser shows how to efficiently implement those rules in an SGLR parser, by passing a bitfield up the parse tree as it is being constructed. This bitfield stores which kind of nodes are in left- and rightmost spines of that parse tree, which determines which parents are allowed.

In this post I'll investigate an alternative way to do disambiguation that is based on disambiguating individual unions `A | B` and sequential compositions `A B` in the grammar, rather than filtering certain tree patterns out of a parse forest.

The union `A | B` will produce ambiguity whenever there is an input that can be parsed by both `A` and `B`. This is easily resolved by introducing a left-biased choice `A / B` that will try `A` first and only try `B` if `A` fails. This is functionally identical to a precedence filter that filters out `B`-trees in favour of `A`-trees. The difference is our perspective: we think of `A / B` as an unambiguous version of `A | B`, rather than as a filter that filters a parse forest.

The sequential composition `A B` can also produce ambiguity. For example, if `A = B = 'x' | 'xx' | 'xxx'` then the string `xxxx` can be parsed as `(x)(xxx)` or `(xx)(xx)` or `(xxx)(x)`. There is ambiguity about how much of the string is parsed by `A` and how much by `B`. Hence we introduce left-biased sequential composition `A > B`, which always parses as much as possible with `A`, and right-biased sequential composition `A < B`, which always parses as much as possible with `B`. The string `xxxx` will be parsed as `(xxx)(x)` by `A > B` and as `(x)(xxx)` by `A < B`.

That's all well and good, but can we actually do associativity and precedence with those operators? It turns out that we can:

{% highlight fsharp %}
E  ->  E > '+' E  /  E < '*' E  |  'n'
{% endhighlight %}

This will parse `+` as right-associative, `*` as left-associative, and gives higher precedence to `*`. Note that the precedence and associativity of `<`,`>`,`/` is such that the grammar is parsed as follows:

{% highlight fsharp %}
E  ->  (E > ('+' E))  /  (E < ('*' E))  |  'n'
{% endhighlight %}

Here's a CYK-parser written in F# that implements this:

{% highlight fsharp %}
type Node = Str of string | Sym of string | AltL of Node * Node | SeqL of Node * Node | SeqR of Node * Node

let parse grammar (str:string) =
  let cache = new System.Collections.Generic.Dictionary<_,_>()
  let rec parseN N i j =
    match cache.TryGetValue((N,i,j)) with
    | true, v -> v 
    | _ -> 
      let parseSeq A B = Seq.tryPick (fun k ->
          match (parseN A i k,parseN B k j) with
          | Some a,Some b -> Some (a + b) | _ -> None)
      let v = match N with
              | SeqL(A,B) -> parseSeq A B (seq{i + 1..j-1})
              | SeqR(A,B) -> parseSeq A B (seq{j-1..-1..i + 1})
              | AltL(A,B) -> 
                  match parseN A i j with 
                  | Some s -> Some s | None -> parseN B i j
              | Str s -> if j-i=s.Length && str.[i..j-1]=s then Some s else None
              | Sym p -> Option.map (sprintf "%s[%s]" p) (parseN (Map.find p grammar) i j)
      cache.Add((N,i,j),v); v
  parseN (Map.find "S" grammar) 0 (String.length str)  
{% endhighlight %}

We write the arithmetic grammar as follows:

{% highlight fsharp %}
let arithmeticGrammar =
  [
  "S",AltL(
        Str "n", 
        AltL(
          SeqL(Sym "S",SeqL(Str " + ", Sym "S")),
          SeqR(Sym "S",SeqL(Str " * ", Sym "S"))))
  ] |> Map.ofList
{% endhighlight %}

And test it:

{% highlight fsharp %}
> test arithmeticGrammar ["n + n + n";"n * n * n";"n + n * n";"n * n + n";"n * * + n"];;
n + n + n ==> S[n] + S[S[n] + S[n]]
n * n * n ==> S[S[n] * S[n]] * S[n]
n + n * n ==> S[n] + S[S[n] * S[n]]
n * n + n ==> S[S[n] * S[n]] + S[n]
n * * + n ==> Parse error
{% endhighlight %}

With this utility function:

{% highlight fsharp %}
let test g ss = ss |> Seq.iter (fun s -> printf "%s ==> %s\n" s (defaultArg (parse g s) "Parse error"))
{% endhighlight %}

The more difficult examples from the paper involving if-then/if-then-else/match can also be handled by adding left and right bias at appropriate points:

{% highlight fsharp %}
let prefixGrammar =
  [
  "S",AltL(
        Str "n", 
        AltL(
          SeqR(Str "if ", SeqR(Sym "S", SeqR(Str " then ", Sym "S"))),
          SeqL(Sym "S",SeqL(Str " + ", Sym "S"))))
  ] |> Map.ofList

let danglingElseGrammar =
  [
  "S",AltL(
        Str "n", 
        AltL(
          SeqR(Str "if ", SeqR(Sym "S", SeqR(Str " then ", Sym "S"))),
          SeqR(Str "if ", SeqR(Sym "S", SeqR(Str " then ", SeqR(Sym "S", SeqR(Str " else ", Sym "S")))))))
  ] |> Map.ofList

let longestMatchGrammar =
  [
  "S",AltL(
        Str "n", 
        SeqR(Str "match ", SeqR(Sym "S", SeqR(Str " with ", Sym "P+"))));
  "P+",AltL(
          Sym "P",
          SeqL(Sym "P", SeqL(Str " ", Sym "P+")));
  "P",SeqL(Str "id -> ", Sym "S")
  ] |> Map.ofList 
{% endhighlight %}

Testing gives:

{% highlight fsharp %}
> test prefixGrammar ["n + if n then n + n"];;
n + if n then n + n ==> S[n] + S[if S[n] then S[S[n] + S[n]]]

> test danglingElseGrammar ["if n then if n then n else if n then n else n"];;
if n then if n then n else if n then n else n 
==> if S[n] then S[if S[n] then S[n] else S[if S[n] then S[n] else S[n]]]

> test longestMatchGrammar ["match n with id -> match n with id -> n id -> n"];;
match n with id -> match n with id -> n id -> n 
==> match S[n] with P+[P[id -> S[match S[n] with P+[P[id -> S[n]] P+[P[id -> S[n]]]]]]]
{% endhighlight %}

Note that at most points in those grammars, it doesn't matter whether we use left bias (SeqL) or right bias (SeqR), because those parts of the grammar are already unambiguous. For instance, `(X '+')` can be parsed in only one way, namely, for a given input string `"something+"`, the `"+"` will be consumed by `'+'` and the rest will be consumed by `X`. This toy parser only supports SeqL and SeqR, so we must choose either `(X < '+')` or `(X > '+')`, but for a real implementation we'd want to add a version of Seq written `(X '+')` that creates a parse forest with all alternatives, and/or raises an error if there is more than one parse tree, telling us that we need to disambiguate that particular sequential composition.

For repetition `Y = A*`, this method of disambiguation can support leftmost-longest, leftmost-shortest, rightmost-longest, and rightmost-shortest:

{% highlight fsharp %}
Y -> ε | A > Y      // leftmost-longest
Y -> ε | A < Y      // leftmost-shortest
Y -> ε | Y < A      // rightmost-longest
Y -> ε | Y > A      // rightmost-shortest
{% endhighlight %}

Note that that `<` and `>` are not associative, `A > (B > C)` is not the same as `(A > B) > C`:

{% highlight fsharp %}
let nonAssociativeGrammar1 =
  [
  "S",SeqL(Sym "A", SeqL(Sym "B", Sym "C"));
  "A",AltL(Str "aaaa", Str "aaa");
  "B",AltL(Str "a", Str "abbb");
  "C",AltL(Str "b", Str "bbbb")
  ] |> Map.ofList 

let nonAssociativeGrammar2 =
  [
  "S",SeqL(SeqL(Sym "A", Sym "B"), Sym "C");
  "A",AltL(Str "aaaa", Str "aaa");
  "B",AltL(Str "a", Str "abbb");
  "C",AltL(Str "b", Str "bbb")
  ] |> Map.ofList

> test nonAssociativeGrammar1 ["aaaabbbb"];;
aaaabbbb ==> A[aaa]B[a]C[bbbb]

> test nonAssociativeGrammar2 ["aaaabbbb"];;
aaaabbbb ==> A[aaa]B[abbb]C[b]
{% endhighlight %}


A CYK parser is not great, but any parser that can produce a parse forest annotated with an input range `i..j` for each node in the parse forest can be modified to support this kind of disambiguation. This method has no problems with filtering too much or too little, since it always produces a single parse tree, and works for any context free grammar. The question is whether biased choice and left and right biased sequential composition are enough to express all the disambiguation we want to do in practice. It might be that  the disambiguation we want can be expressed by filtering certain tree patterns out of the parse forest, but can't be expressed by inserting `<` and `>`. In those cases we still have to rewrite the grammar to make it produce the parse tree we want.