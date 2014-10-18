---
layout: post
title:  "The best collections library design, part 2"
date:   2014-10-18 16:33:40
categories: 
---

In the previous post we've looked at collection libraries of various languages, and concluded that we need a sequence abstraction. In this post we will evaluate the pros and cons of various options. A sequence abstraction will need to support operations such as `map`, `filter`, `flatmap`, `scanl`, `takeWhile`, and more. As we will see, not all sequence abstractions support all those operations, and that's where there's trade-offs to be made.

## Lazy lists ##

One candidate are lazy lists. I'm going to use the strict language F# for this, to make it explicit where the laziness is happening. To define lazy lists we first need lazy values. 

{% highlight fsharp %}
type Lazy<'t> = Lazy of (unit -> 't)

let delay f =
    let cache = ref None
    Lazy(fun () -> match !cache with 
                   | None -> let x = f() in cache := Some x; x
                   | Some x -> x)
                   
let force (Lazy f) = f ()
{% endhighlight %}

We define a type `Lazy<'t>` which has two operations:

{% highlight fsharp %}
delay : (unit -> 't) -> Lazy<'t>
force : Lazy<'t> -> 't
{% endhighlight %}

`delay` creates a lazy value from a function. The function is not executed until `force` is called on that lazy value. `force` also caches the result, so that if `force` is called on the same lazy value multiple times, it only performs the computation once.

Using this we can define the type of lazy lists:

{% highlight fsharp %}
type Node<'t> = Cons of 't * List<'t> | Nil
and List<'t> = Lazy<Node<'t>>
{% endhighlight %}

Note that `Lazy` is also around the outer layer. This is important to make the list fully lazy. In particular, this would be incorrect:

{% highlight fsharp %}
type List<'t> = Cons of 't * Lazy<List<'t>> | Nil
{% endhighlight %}

Because for this type the outermost layer is a `Cons/Nil`, which is not wrapped in `Lazy`. We define `map`:

{% highlight fsharp %}
let rec map f xs = delay (fun () -> 
    match (force xs) with
    | Cons(x, xs') -> Cons(f x, map f xs')
    | Nil -> Nil)
{% endhighlight %}

### Pros and cons of lazy lists ###

A nice property of lazy lists are that they are a pure value, they support many sequence operations, and they can represent infinite sequences. That said, they also have several disadvantages:

1. They can easily cause memory leaks. An innocuous function like `average xs = sum xs / length xs` causes a memory leak: the whole sequence `xs` is built up in memory during the `sum`, and then that sequence is traversed again in `length`. This means that there is a time at which the entire sequence has to be present in memory, and it can't be garbage collected until `length` is done.
2. Lazy lists create a lot of garbage even when there is no memory leak. This is mitigated by compiler optimizations such as stream fusion, but relying on compiler magic for performance is a not ideal. Predictable performance is important. Ideally the sequence abstraction should not create garbage *by construction*, so that if you write your algorithms in terms of the sequence abstraction, you're guaranteed not to put pressure on the GC.
3. They do not support parallel execution. A lazy list is an inherently sequential structure. In order to get to the next element you traverse a pointer. Consider mapping the function `x -> x+1` over a big array. In principle this can be done in parallel by dividing the array into chunks. But if we transform the array to a lazy list, then `map` and then transform it back to an array, we've lost the parallelism.
4. They do not support resource cleanup. If we want to process a file we want to close that file at the end of that process. Lazy lists do not support any deterministic way to clean up resources when the operations are done.
5. They cannot represent push collections, such as event streams.
6. Effects on lazy list operations, like mapping over a list with an effectful function f, are questionable because of the unpredictable order of execution.
7. It does not support `drop` and `dropWhile` in an efficient way: you have to traverse the entire front of the list just to skip over elements.

## Iterators ##

Many imperative languages have the concept of iterator. I'll use Python as an example. In Python an iterator is stateful object an object with a `next()` method, which returns the value of the current element and advances the state to the next element. When the iterator is at the end, `next()` throws a `StopIteration()` exception. This is just a way to encode returning an optional element: `next : () -> Maybe a`. Iterators in Python support generator comprehensions, which are like list comprehensions except they work over iterators. Iterators can also be consumed by for loops:

{% highlight python %}
for elem in iter:
    ...
{% endhighlight %}

Python has language support for creating iterators using the `yield` statement. This lets you easily define iterators with just a function:

{% highlight python %}
def range(n,k):
    i = n
    while i < k:
       yield i
       i += 1

for j in range(10,20):
    print j
{% endhighlight %}

A `map` function can be defined easily:

{% highlight python %}
def map(f, xs):
    for x in xs:
    yield f(x)
{% endhighlight %}

Iterators have the benefit that to do iteration they do not need to allocate anything. Like lazy lists, they can support infinite sequences. Like lazy lists, they don't support deterministic resource cleanup, effectful iterators are questionable, they don't support push collections, and they do not support parallel execution. Iterators do not cause memory leaks like lazy lists do, but they have other problems. Suppose we wrote

{% highlight python %}
xs = ... some iterator ...
average = sum(xs) / length(xs)
{% endhighlight %}

This will not cause a memory leak, but it will not get the right answer. Iterators are stateful, and the `sum(xs)` has already fully consumed the iterator `xs`. This means that the `length(xs)` won't work. Python's `itertools` module does have a function that will clone an iterator, called `tee()`.

{% highlight python %}
xs = ... some iterator ...
xs1, xs2 = tee(xs)
average = sum(xs1) / length(xs2)
{% endhighlight %}

Tee sets up a dequeue. Every time one of its output iterators are advanced, it will add/remove from the dequeue as neccessary. If its output iterators are iterated over in tandem, then this operates in constant space. If one of its output iterators is first fully used, and after that the second iterator is fully used, then tee has to buffer the entire sequence in the dequeue. That's what's happening in the above example: it has the same memory leak as the lazy list version: `tee()` will fully build the dequeue. At least the memory leak is explicit now...

## C++ iterators ##

C++ has an elaborate iterator model:

* Input iterators: single pass iterators, much like Python iterators and C# IEnumerators
* Forward iterators: iterators that can be copied
* Bidirectional iterators: an iterator that can move backward as well as forward
* Random access iterators: iterator that can jump to any index
* Output iterators: iterator that can only be written to

C++ iterators can be mutable or immutable. Mutable iterators can be used to modify the underlying collection at the index that the iterator is currently pointing to.

## IEnumerable/IEnumerator ##

C# has an interface IEnumerator, which represents an iterator in a slightly different way (using Current and MoveNext() methods), but this difference is immaterial. The real difference with iterators is that an `IEnumerator` has a `Dispose` method, which you should call when you are done with it. This allows the `IEnumerator` to clean up any resources like file handles.

{% highlight csharp %}
interface IEnumerator<T>
{
    T Current { get; }
    bool MoveNext();
    void Dispose();
}
{% endhighlight %}

The C# designers had a brilliant idea: you shouldn't work directly with IEnumerators, you should work with IEnumerator *factories*. That's what IEnumerable is:

{% highlight csharp %}
interface IEnumerable<T>
{
    IEnumerator<T> GetEnumerator();
}
{% endhighlight %}

The collection operations work on IEnumerable, not on IEnumerator! Suppose you have a pipeline like this:

{% highlight csharp %}
xs.Select(x => x+1).Where(x => x < 100).Select(x => x*2).Sum()
{% endhighlight %}

(in C#, map is called Select, and filter is called Where)

This constructs an IEnumerable pipeline, but it does not actually run the pipeline until `Sum()` is called. `Sum` will call `GetEnumerator` on the `.Select(x => x*2)`, which will in turn call `GetEnumerator` on `.Where(x => x < 100)`, which will call `GetEnumerator` on `.Select(x => x+1)`, which will call `GetEnumerator` on `xs`. That process sets up the `IEnumerator` (iterator) pipeline. Once `Sum` is done summing, it will `Dispose` the iterator that it's iterating over, which calls `Dispose` on the previous iterator in the pipeline, and so forth. If `xs` represents a file, then the file can be opened when `GetEnumerator` is called, and closed when `Dispose` is called, so we have the ability to do resource cleanup.

What happens when we try to compute an average?

{% highlight csharp %}
var average = xs.Sum() / xs.Count();
{% endhighlight %}

This will create the iterator pipeline twice. If `xs` is itself a pipeline, then all the operations in that pipeline will be executed twice. That's something to keep in mind with IEnumerables: they represent computations that can be executed, not collections that are data. If you want to buffer, you have to explicitly convert your IEnumerable to an array and back. This architecture means that we also get more predictable effectful operations. If we do this:

{% highlight csharp %}
var ys = xs.Select(x => EffectfulFunction(x))
{% endhighlight %}

then `ys` represents a *computation* that has effects when executed. Those effects are executed in a predictable manner, but one has to keep in mind that IEnumerables represent computations.

The benefits of IEnumerable:

1. IEnumerables are pure values.
2. IEnumerable takes care of resource handling.
3. Effects are executed in a predictable manner.
4. No implicit memory leaks.
5. No memory allocation for iteration.

The main disadvantage of IEnumerable is that like lazy lists and iterators, they do not support parallelism nor push collections nor efficient drop/dropWhile.

## IObservable/IObserver ##

The third party C# library [Rx](http://msdn.microsoft.com/en-us/data/gg577609.aspx) provides the equivalent of IEnumerable/IEnumerator for push collections. Push collections are collections where the producer rather than the consumer is in charge of when elements go through the pipeline. An example is a GUI button with an event handler that handles clicks. You can view the event stream of clicks as a collection. Since we can't control when a user will click the button, the producer is in charge of pushing elements through the pipeline. Compare with IEnumerable where the consumer such as `Sum()` is responsible for pulling elements out of the pipeline. When you've built up an IObservable pipeline, you can use it by subscribing an event handler on it. Here's an example:

{% highlight csharp %}
var button = new Button();
...
var clicks = button.Clicks;
var leftClicks = clicks.Where(click => click.IsLeftClick);
var leftClickPositions = leftClicks.Select(click => click.Position);
leftClickPositions.Subscribe(pos => Console.WriteLine(pos));
{% endhighlight %}

This creates an event stream of clicks, takes only the left clicks, then maps each click to its position, and subscribes an event handler that prints each position to the console.

IObservable has all the advantages and disadvantages of IEnumerable, except it works on push collections rather than pull collections.

## Folds/Reducers/Transducers ##

The new hotness is Clojure's reducers and transducers. Reducers and transducers make use of an isormophism between lists and folds. I'm going to use Haskell syntax to explain them, because it's easier to understand that way.

For (lazy) lists we have three types of things we are working with:

1. Lists producers: `[a]`, these can be constructed from a collection, or by some generating function like `range n k`.
2. List transformers: `[a] -> [b]`, like `map f`, `filter p`, `flatmap f`, `scanl f x` and `take n`.
3. List consumers: `[b] -> r`, like `sum`, `length` and `fold f x`.

So we have:

       [a]          [a] -> [b]       [b] -> r
    producers      transformers      consumers

List consumers can be written as a fold: `sum = fold (+) 0`, `length = fold (+1) 0` etc. The `fold` has an accumulation function as an argument of type `(state -> b -> state)`, and an initial `state`. This brings us to the idea to represent consumers as a fold:

{% highlight haskell %}
data FoldFn b state = FoldFn (state -> b -> state) state
{% endhighlight %}

For some fold operations the state is not actually what we want to return. For example to compute the `average` function, we may want to accumulate a pair of `(sum, length)` as the state:

{% highlight haskell %}
fold (\(sum,length) x -> (sum+x, length+1)) (0,0)
{% endhighlight %}

But eventually we want to return the average `sum / length`. To do that we create a type `Fold` that represents the final fold with one additional operation `state -> r`:

{% highlight haskell %}
data Fold b state r = Fold (FoldFn b state) (state -> r)
{% endhighlight %}

However, there is no reason to expose the state in the type. We can hide it with an existential:

{% highlight haskell %}
data Fold b r = forall state. Fold (FoldFn b state) (state -> r)
{% endhighlight %}

We can represent a fold that computes the average as follows:

{% highlight haskell %}
average :: Fold Float Float
average = Fold averageAccum (\(sum,length) -> sum / length)
      where averageAccum = FoldFn (\(sum,length) x -> (sum+x, length+1)) (0,0)
{% endhighlight %}

We can use this to compute the average of a list:

{% highlight haskell %}
foldList :: Fold a r -> [a] -> r
foldList (Fold (FoldFn f init) final) xs = final (fold f init xs)

foldList average [1,2,3,4]
{% endhighlight %}

That's the consumer side, how about producers? By analogy with lists: if `[a]` is a list producer, then `[a] -> r` is a list consumer. If `Fold a r` is a consumer, then `Fold a r -> r` is a producer! Lets call this type Unfold:

{% highlight haskell %}
data Unfold a = forall r. Unfold (Fold a r -> r)

listToUnfold :: [a] -> Unfold a
listToUnfold xs = Unfold (\fld -> foldList fld xs)
{% endhighlight %}

What about the transformers? I'll call the transformers Refold, and they transform FoldFn's:

{% highlight haskell %}
data Refold a b = forall c. Refold (FoldFn a c -> FoldFn c b)
{% endhighlight %}

Note that in Clojure terminology, Unfolds are reducers, and Refolds and Folds are transducers (combining them into one is a design mistake if you ask me).

We can define composition functions that compose Refolds, Unfolds and Folds:

{% highlight haskell %}
Refold a b -> Refold b c -> Refold a c
Unfold a -> Refold a b -> Unfold b
Refold a b -> Fold b r -> Fold a r
{% endhighlight %}

I'll leave this as an exercise for the reader. To complete the analogy with lists:

     Unfold a       Refold a b       Fold b r
    producers      transformers      consumers

We can define

{% highlight haskell %}
map :: (a -> b) -> Refold a b
filter :: (a -> Bool) -> Refold a a
flatmap :: (a -> [b]) -> Refold a b
{% endhighlight %}

Though it would of course be more appropriate to define flatmap like this, to stay true to our new sequence abstraction:

{% highlight haskell %}
flatmap :: (a -> Unfold b) -> Refold a b
{% endhighlight %}

See also [Tekmo's foldl library](https://hackage.haskell.org/package/foldl).

### Advantages & Limitations ###

This abstraction has several advantages:

1. It supports writing `average` compositionally and without memory leaks.
2. It supports parallelism: a Refold operation can be executed in parallel.
3. It supports both push and pull collections: Refold can work for both push and pull
4. It executes pipelines without any memory allocation.
5. You can execute effects deterministically (at least in an impure language).

It also has several disadvantages:

1. It does not support automatic resource handling.
2. It does not support `take`, `takeWhile`, `drop`, `dropWhile` in an efficient way.
3. It does not support `scanl`, or stateful transformers in general.
3. It does not support `zip`: there's no efficient way to combine `Unfold a -> Unfold b -> Unfold (a,b)`.

Some of these are easily addressed: resource handling can be added. Efficient `take` and `takeWhile` can be added: you can add early stopping to FoldFn: instead of `state -> x -> state` you do `state -> x -> Maybe state`, where `Nothing` indicates that we want to terminate. You can add a way to keep state accross elements in Refolds, to support `scanl`. More generally you can upgrade Fold to support any monadic effect. In Clojure, native mutable state is used for stateful transducers.

Once you add these features you can no longer support parallelism however. You need to make a choice: either you have left folds and stateful transformers, and not parallelism, or you have associative folds and stateless transducers but you get parallelism. (you could have an associative version of scan that does a parallel prefix sum)

There are many other options, like pipes or conduits, iteratees, enumeratees, etcetera. These all support some subset of the operations with a certain level of efficiency, but none are perfect on all points.

## Fundamental tensions ##

We would like to support all operations in all contexts (push, pull, parallel, and others), without any allocation, and all the other desiderate we've talked about. This is impossible: a stateful transformer is fundamentally incompatible with parallelism, for example. Zipping is incompatible with push collections & no memory allocation, and unzipping is incompatible with pull collections & no memory allocation. It seems that we'll have to implement different abstractions for different contexts. We need push collections, with all the operations they support, pull collections with all the operations they support, parallel collections with all the operations they support, and maybe more for different circumstances.

This is unfortunate, because even though there are differences, there are also a lot of commonalities. All three support `map` & `filter`, for example. Moreover, we'd like to support `map` in a broader context than just sequences. There are many types that can be mapped (i.e. are an instance of Functor):

1. `Maybe a`
2. `Either a b`
3. An infinite lazy binary tree
4. Functions `a -> b`

We would like to be able to map pipelines `map f . map g` over infinite binary trees without building an infinite intermediate lazy binary tree in the middle. We should be able to do filter pipelines `filter p . filter q` without intermediate allocations too. Even mixes `map f . filter p . map g` should be no problem. You could try to be clever here, and flatten the binary tree to a sequence by interleaving the left & right subtrees, and then at the opposite end of the pipeline "uninterleave" the sequence back into a binary tree. That would make it terminate, but it would still be very inefficient. What if we only needed one path down the resulting binary tree? Then we would need to skip over many sequence elements. No, the reality is a universal sequence abstraction isn't going to cut it.

## Glimmer of hope ##

You probably already got where we're going here. Instead of composing producers, like iterators/enumerables, and instead of composing consumers, like folds, we compose transformers. We use laws such as:

{% highlight haskell %}
map f . map g = map (f . g)
filter p . filter q = filter (\x -> p x && q x)
{% endhighlight %}

as the *definition* of `map` and `filter`. To support multiple different operations we need to find a more general representation that can represent all such compositions:

{% highlight haskell %}
filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap f . filterMap g = filterMap (combine f g)
    where combine f g x = case f x of
                          | Nothing -> Nothing
                          | Just y -> g y

map f = filterMap (Just . f)
filter p = filterMap (\x -> if p x then Just x else Nothing)
{% endhighlight %}

We compose transformers, and the type of the composition is as specific as possible, so that it can be used in as many contexts as possible. Any context that supports `map` can support a composed pipeline of `map`'s. Any context that supports `filter` can support a composed pipeline of `filters`. Any context that supports `filterMap` can support a composed pipeline of `map`'s and `filter`'s.

More on this in part 3.