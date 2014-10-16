---
layout: post
title:  "The best collections library design, part 1"
date:   2014-10-16 16:33:40
categories: 
---

Collections are the centerpiece of the standard library of a programming language. If there's any library that's important to get right, it's the collections library. Yet designs in different languages differ greatly, and some are far better than others. In this series I will explore the design space of collections libraries and evaluate the pros and cons of each design.

There are many different types of collections: lists, arrays, sets, bags, maps (both sorted and hash based variants), queues, stacks, heaps, and more. These represent different data, allow different operations, and even when they allow the same operations they may have different efficiency. Some languages even have multiple variants of each collection, like mutable and immutable. On the other hand, these collections support many common operations such as iteration, filter, map, and fold. In this episode I'm going to focus on those kinds of operations.

## The story of map ##

The map function is one of the core operations of a modern collections library:

{% highlight haskell %}
map : (a -> b) -> CollectionType a -> CollectionType b
{% endhighlight %}

This also goes by the name collect (Smalltalk) and Select (C#). It takes a function, and transforms a collection by applying that function to each element. Simple, right? I'm going to show you why this type for map is **wrong** for a collections library.

### Map in Haskell ###

For lists, arrays, stacks and queues everything is fine:

{% highlight haskell %}
map : (a -> b) -> List a -> List b
map : (a -> b) -> Stack a -> Stack b
etc.
{% endhighlight %}

The problems start to show when we try sorted sets:

{% highlight haskell %}
map : Ord a,b => (a -> b) -> Set a -> Set b
{% endhighlight %}

Elements in sorted sets need to support a comparison operation. That's what the `Ord a,b` is saying. It gets even worse when we look at strings:

{% highlight haskell %}
map : (Char -> Char) -> Text -> Text
{% endhighlight %}

Since strings always contain characters, the function must also return characters in order to transform a string. In Haskell this kind of problem shows up in the Functor, Monad, Traversable and Foldable type classes. There is a [MonoFunctor/MonoTraversable/MonoFoldable package](https://hackage.haskell.org/package/mono-traversable) that tries to solve this problem by defining a different kind of traversable/foldable that works on collections such as strings. Those type classes aren't a replacement for the old ones, since they only allow operations of type `(a -> a)` and in general map can support `(a -> b)`. Those type classes also do not do anything to solve the problem of sets. For that we could introduce yet another set of type classes OrdFunctor/OrdTraversable/OrdFoldable. Then we encounter hash based sets, and we need HashFoldable/HashTraversable/HashFunctor. Not good. What about consuming one collection and producing another?

{% highlight haskell %}
map : (Char -> a) -> Text -> List a
map : Ord b => (a -> b) -> List a -> Set b
{% endhighlight %}

Clearly this doesn't scale, especially if you consider operations that work on multiple collections, such as append `(++)`, zip, flatten and flatmap.

### Map in Scala ###

Scala takes an even more ambitious approach. It will try to upgrade your collection based on the function you're mapping (or downgrade, depending on your point of view). If you are mapping a `Char -> Char` function over your string, the output will be a string. However if you are mapping a `Char -> Int` function  over your string, your output will suddenly become a `Vector[Int]`. Similarly, if you map a function over a SortedSet and the resulting elements do not support ordering, then your set will be downgraded to a non-sorted set. This is a "just do the right thing" system. Problem solved! The **correct** type of `map` is:

{% highlight scala %}
def map[A, B, That](f: A => B, coll: FilterMonadic[A, Repr])(implicit bf: CanBuildFrom[Repr, B, That]): That
{% endhighlight %}

Back to reality! The Scala documentation displays bizarre types such as the type of `String.map` being `map[B](f: (A) ⇒ B): String[B]`. What's a `String[B]`? It doesn't exist. The real type of map is `String.map[B, That](f: (Char) ⇒ B)(implicit bf: CanBuildFrom[String, B, That]): That`. This complicated machinery is needed for Scala to upgrade/downgrade your collections when mapping. If you thought that was complicated consider that Scala has subtyping too, and types may be co- and contravariant. What happens if you concatenate a `List[Int] ++ SortedSet[Int]` (answer: you get a list). What if you change the order and concatenate a `SortedSet[Int] ++ List[Int]` (answer: you get a sortedset). Now consider that the parameter type itself may be different and may or may not support comparison `SortedSet[T] ++ List[Q]`. Next consider that the concrete type of a value may be a subtype of the static type of the value. So what happens if we put a `List[Int]` and a `SortedSet[Int]` and another `SortedSet[Int]` in some order together in a `List`, and then fold the `++` operator over that? What about flatmap of `A => SortedSet[B]` over a `List[A]`, what's the result type of that? The concrete type of the result will be some function of the static types and the concrete types and the order in which they appeared in the list, and the static type will be some function of the static types.

Here's a puzzle for you:

{% highlight scala %}
def sumBy[A](f:(A => Int), xs:Traversable[A]) = xs.map(f).sum

sumBy((s:String) => s.length, Set("hello", "my", "world"))
{% endhighlight %}

What does that return? We are summing the elements by length. The length of the strings is 5+2+5 = 12. Right? No: the sumBy function first maps over the collection, creating a collection of lenghts. In this case that will be `Set(5,2,5)`, but sets don't have duplicates! So that becomes `Set(5,2)` and sumBy returns 7. Had we used List instead of Set, the answer would have been 12, of course. All that complexity, and the end result is not "just do the right thing", the result is broken abstractions...

### Map in Scheme ###

In Scheme each data type comes with its own map function. You have list-map, vector-map, set-map, etc. This is clearly not a good approach either, because it requires a different function for each (collection,operation) pair. And what if you want to map a function over a list, but get a vector out? It would be wasteful to map a function over the list to produce an intermediate list, and then convert that intermediate list into a vector.

### Map in Ruby and Python ###

In Ruby and Python `map` always returns an array. Map over an array? Get an array back. Map over a string? Get an array back. Map over a set? Get an array back. Believe it or not, this is much closer to the best design than any of the other solutions we've talked about so far! This still has a big disadvantage: if you chain map multiple times then on each step you build an intermediate collection. If you do `xs.map{|x| x*2}.map{|y| y+1}` then one useless intermediate array is built. It would be much better to execute `xs.map{|x| x*2 + 1}`. The same goes for all operations that create intermediate arrays: map, filter, zip, flatmap, etc.

## What is not the best collections library design ##

We have already figured out a few examples of what not to base a collections library on:

1. Haskell's traversable/foldable/functor, or mono- or ord- or hash- versions of those
2. Scala's system where the result type is chosen with magic rules
3. Scheme's different set of functions for each collection
4. Ruby and Python's always return an array

Here are some of the requirements of a good collections library:

1. It should support each operation for any collection
2. It should not have any magic rules by which the type of intermediate collections is determined. In fact, it should not build any intermediate collections for chains of multiple operations *at all*.
3. You should be able to put any collection type in, and get any collection type out, without the overhead of an additional conversion
4. Operations that operate multiple collections such as `zip`, `append`, `flatten`, and `flatmap` should be able to work on any combination of collections types, e.g. you should be able to `zip` or `append` a vector and a sorted set, and then apply fold to the result of that

## The solution ##

The collection operations should not be implemented on the collections themselves, they should be implemented on a sequence abstraction `Seq a`. We get these types:

{% highlight haskell %}
map : (a -> b) -> Seq a -> Seq b
filter : (a -> bool) -> Seq a -> Seq a
flatmap : (a -> Seq b) -> Seq a -> Seq b
fold : (s -> a -> s) -> s -> Seq a -> s
zip : Seq a -> Seq b -> Seq (a,b)
etc.
{% endhighlight %}

In addition we define conversions to and from each collection type:

{% highlight haskell %}
fromList : List a -> Seq a
toList : Seq a -> List a

fromSet : Ord a => Set a -> Seq a
toSet : Ord a => Seq a -> Set a

fromString : String -> Seq Char
toString : Seq Char -> String
{% endhighlight %}

A collection only needs to support conversions to and from `Seq` to support the complete collections API. We avoid combinatorial complexity explosion and broken abstraction barriers. The collection operations such as `map` and `filter` can be implemented on `Seq` without constructing fully realized intermediate collections. This gives us efficient composition of multiple operations in a pipeline. With the right sequence type the conversion to and from other collection types is also cheap, so that doing `fromSet.map(\x -> f x).toSet` is just as fast as a direct map on a set would be.

In the next episode I will look at languages that already have a universal sequence abstraction, and I will compare different sequence abstractions such as lazy lists, iterators, unfolds and folds.