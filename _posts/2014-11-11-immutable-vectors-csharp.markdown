---
layout: post
title:  "Optimizing immutable vectors in C#"
date:   2014-11-11 16:33:40
categories: 
---

In the last post I talked about immutable stacks & queues. This post will be on immutable vectors. We want to support 3 operations:

{% highlight csharp %}
public interface Vector 
{
    T Lookup(int i);
    Vector Add(T x);
    Vector Set(int i, T x);
}
{% endhighlight %}

Lookup finds an element at index `i`, Add takes a vector of size `n`, and returns a vector of size `n+1` with the additional element added to the end, and Set returns a new vector which has the new value `x` at index `i`. I've tried many different implementations (check out [this ImmutableCollections github repository](https://github.com/julesjacobs/ImmutableCollections/tree/master/ImmutableCollections/ImmutableCollections/Vectors) and check out [Sandro Magi's Sasa repository](http://sourceforge.net/p/sasa/code/ci/default/tree/Bench/) which contains several other vector implementations by him & me). In the end there were two implementations that were better than the others in my benchmarks.

## ResizeVector ##

The first implementation is a tree with a fixed branching factor n (currently n=32). A tree of height h can store 32^h elements. When an element is added to a full tree, an additional level is added on top of the root. This means that unlike most tree data structures, this tree grows from the root up rather than from the leaves down. The representation in C# is as follows:

{% highlight csharp %}
struct Node<C> : IVec where C : struct, IVec
{
    C[] children;

    ... operations ...
}

struct Leaf : IVec
{
    T item;

    ... operations ...
}
{% endhighlight %}

A tree of height 3 is represented as `Node<Node<Node<Leaf>>>`. Such a tree structure is then wrapped in a wrapper class that enables polymorphism over the tree height:

{% highlight csharp %}
public interface Vector 
{
    T Lookup(int i);
    Vector Add(T x);
    Vector Set(int i, T x);
}

class Vector<V> : Vector where V : struct, IVec
{
    V self;

    ... operations ...
}
{% endhighlight %}

A vector with internal representation of height 3 is `Vector<Node<Node<Node<Leaf>>>>`. That is then upcasted to the public interface `Vector`. The `Vector` class also takes care of resizing the tree height when an element is added to a full tree.

## MergeVector ##

A disadvantage of ResizeVector is that we need to copy the path from the root to the rightmost leaf when adding an element to the end. If the tree is of height 6, then we need to copy 6 arrays of 32 elements to add an element at the end. It would be better to add a buffer in front of the tree that accumulates an array of 32 items, and then only appends that to the big tree once. That way we only need to copy a path 1 in 32 times. We can apply that same idea recursively: we keep buffers of size 32, 32^2, 32^3, ... 32^h, each of which is represented as a tree structure. When adding an element we first try to add it to the lowest size buffer. If that buffer is full after adding, we append that buffer to the next size buffer. If that buffer is full too, we append that to the next size buffer, and so forth. In turns out that adding an element to the end is amortized O(1) that way. 

The representation in C# is as follows. We have the same Node/Leaf structure as for the ResizeVector:

{% highlight csharp %}
struct Node<C> : IVec where C : struct, IVec
{
    C[] children;

    ... operations ...
}

struct Leaf : IVec
{
    T item;

    ... operations ...
}
{% endhighlight %}

This is used to represent the trees of height 32^i. In addition we have a struct Root which represents a collection of trees of size 32, 32^2, 32^3 .. 32^h:

{% highlight csharp %}
struct Root<N,R> : IRoot<Node<N>>
    where N : struct, IVec 
    where R : struct, IRoot<N>
{
    public N[] nodes;
    public R next;

    ... operations ...
}

struct End : IRoot<Leaf>
{
    ... operations ...
}
{% endhighlight %}

For example, a tree with 3 buffers is represented as `Root<Node2, Root<Node1, Root<Leaf, End>>>` where `Node2 = Node<Node<Leaf>>` and `Node1 = Node<Leaf>`.

## Benchmarks ##

Here are the results for vectors of size 1 million. The Add benchmark builds the vector by adding 1 million elements to an empty vector, the Set benchmark sets 1 million random elements to a new value, and Lookup does 10 million random lookups. Collections.ImmutableList is Microsoft's implementation.

<table border="1">
<tr><th>Implementation</th><th>Add</th><th>Set</th><th>Lookup</th><th>Memory</th></tr>
<tr><td>Collections.ImmutableList </td><td> 9207 ms </td><td> 26835 ms </td><td> 34778 ms </td><td> 48000024 bytes</td></tr>
<tr><td>ResizeVector </td><td> 1943 ms </td><td> 6806 ms </td><td> 1149 ms </td><td> 5032240 bytes</td></tr>
<tr><td>MergeVector </td><td> 958 ms </td><td> 5378 ms </td><td> 1211 ms </td><td> 5032344 bytes</td></tr>
</table>
<br>

As you can see, MergeVector is the clear winner. It's only slightly slower than ResizeVector on Lookups, but it's much faster on Add and slightly faster on Set. Compared to Microsoft's immutable vector, MergeVector is about 10x faster on Add, 5x faster on Set, 29x faster on Lookup. Microsoft's vector also uses 10x more memory. 

If the description of the vectors is unclear, please let me know, and I can do a more in-depth post about how they work exactly. You can also read the [source code and the benchmarks](https://github.com/julesjacobs/ImmutableCollections/tree/master/ImmutableCollections/ImmutableCollections/Vectors). The repository also contains immutable queues, sorted maps and hash maps that are several times faster than Microsoft's immutable collections. In fact, the immutable sorted map is faster than .NET's built in *mutable* sorted map. These are just a proof of concept implementations. If there's interest in a full featured production quality version, I may implement that.