---
layout: post
title:  "Optimizing immutable stacks & queues in C#"
date:   2014-10-25 16:33:40
categories: 
---

Microsoft released an [immutable collections library](https://www.nuget.org/packages/Microsoft.Bcl.Immutable/1.0.34) on NuGet. It contains immutable stacks, queues, vectors, sorted maps & sets, and hash maps & sets. I reimplemented immutable stacks and queues to see if we can go faster.

## Immutable Stacks ##

An immutable stack supports the following operations:

{% highlight csharp %}
class Stack<T>
{
    bool IsEmpty { get ; }
    Stack<T> Push(T x);
    Stack<T> Pop(out T x);
}
{% endhighlight %}

In addition there should be a way to get an empty stack. The benchmark that I will use is the following:

1. We start by putting an int on the stack, for example 25.
2. We repeatedly pop the top of the stack, k, and then we push 1..k-1.
3. We terminate when the stack is empty.

For example when we start with 4, it goes like this:

    4
    3 2 1
    2 1 2 1
    1 1 1 2 1
    1 1 2 1
    1 2 1
    2 1
    1 1 1
    1 1
    1
    end

You can imagine that this creates quite a long process of pushing and popping when you start with a big number:

    25
    24 23 22 21 ... 3 2 1
    etc


### Linked list stack ###

The most obvious implementation is as a linked list. I wrap all data types in a struct in the style of ML functors:

{% highlight csharp %}
struct LinkedListStack<T>
{
	public abstract class Stack 
	{
		bool IsEmpty { get ; }
	    Stack Push(T x) { ... };
	    Stack Pop(out T x);
	}

	class Node : Stack 
	{
		T item;
		Stack rest;
		...
	}
	class End : Stack { ... }

	public static Stack Empty = new End();
}
{% endhighlight %}

We represent an empty stack with `new End()`, Push allocates a new node that points to the rest of the stack, and Pop just follows the `rest` pointer. We can also represent the end of the stack with `null`. Because we can't invoke methods on `null`, we have to wrap it in a struct, so that we can do `Empty.Push(x)` and `Empty.IsEmpty`. Here's the full implementation:

{% highlight csharp %}
struct NullLinkedListStack<T>
{
    public struct Stack
    {
        Node self;

        public bool IsEmpty { get { return self == null; } }

        public Stack Push(T x)
        {
            return new Stack { self = new Node(x, self) };
        }

        public Stack Pop(out T x)
        {
            x = self.item;
            return new Stack { self = self.rest };
        }
    }

    sealed class Node
    {
        public T item;
        public Node rest;

        public Node(T x, Node r)
        {
            item = x;
            rest = r;
        }
    }

    public static Stack Empty = new Stack();
}
{% endhighlight %}

### Buffered stack ###

It seems hard to do better than this: pushing is allocating 1 object, and popping is dereferencing 1 object. How can we possibly push with less than 1 allocation or how can we pop with less than 1 pointer dereference? We can exploit C#'s value types. The idea is to represent the stack with a struct and optionally store the top of the stack inside that struct:

{% highlight csharp %}
public struct Stack
{
    int count;
    T item;
    Node rest;
    ...
}

class Node
{
    public T item1;
    public T item2;
    public Node rest;
    ....
}
{% endhighlight %}

The stack starts out empty, with `count = 0`, and `rest = null`. When we push an element on the stack, we store it in `item` in the struct. So we don't need to do any allocation, because it's a struct! Then when we push another element on the stack, we already have the one stored in `item`, and a new element `x`. Now we create a linked list node with TWO items inside it: `item` and `x`. We can continue like this: every time the stack has an odd number of elements, the top of the stack is stored in the outer struct. We only need to allocate a new list node for half of the pushes! Similarly, we only need to dereference `rest` for half of the pops. Here's an example:


    operation        struct         linked list
    ------------------------------------------
    Empty             -             -

    Push(1)           1             -
    Push(2)           -             (2,1)
    Push(3)           3             (2,1)
    Push(4)           -             (4,3)-(2,1)
    Push(5)           5             (4,3)-(2,1)
    Push(6)           -             (6,5)-(4,3)-(2,1)

    Pop()->6          5             (4,3)-(2,1)
    Pop()->5          -             (4,3)-(2,1)
    Pop()->4          3             (2,1)
    Pop()->3          -             (2,1)
    Pop()->2          1             -
    Pop()->1          -             -

### Benchmarks ###

Here are the results:

<table border="1">
<tr><th>Implementation</th><th>Time</th><th>Memory</th></tr>
<tr><td>Collections.ImmutableStack </td><td> 3028 ms </td><td> 32000000 bytes</td></tr>
<tr><td>LinkedListStack </td><td> 2943 ms </td><td> 32000000 bytes</td></tr>
<tr><td>NullLinkedListStack </td><td> 2851 ms </td><td> 31999936 bytes</td></tr>
<tr><td>BufferedStack </td><td> 8468 ms </td><td> 15999936 bytes</td></tr>
</table>

BufferedStack uses less memory (as expected), but unfortunately it actually runs much slower than a plain linked list. So much for that theory. The best immutable stack is NullLinkedListStack, which is a little bit faster than Microsoft's Collections.Immutable.

## Immutable Queues ##

An immutable queue supports the following operations:

{% highlight csharp %}
class Queue<T>
{
    bool IsEmpty { get; }
	Queue<T> Enqueue(T x);
	Queue<T> Dequeue(out T x);
}
{% endhighlight %}

This is exactly the same as a stack, but the behavior is different: a stack pushes and pops from the same end, a queue enqueues and dequeues from opposite ends. This is a bit more difficult to achieve with an immutable data structure. We can't simply use a linked list, because although we can efficiently put an element on the front of an immutable linked list, we can't efficiently remove an element from the back of a linked list. The standard solution to this is to represent the queue as a pair of stacks `front` and `back`, representing the front of the queue and the back of the queue. When we enqueue an item, we push it onto `back`. When we dequeue an item, we pop it from `front`. The trick is that when `front` is empty, and we want to dequeue an item, we pop all items from `back` and push them on `front` first. Here's an example:

    operation         front         back
    ------------------------------------------
    Empty             -             -

    Enqueue(1)        -             1
    Enqueue(2)        -             2,1
    Enqueue(3)        -             3,2,1
    Enqueue(4)        -             4,3,2,1

    now when we dequeue, we pop all elements from back and push them on the front, 
    effectively reversing the stack:

                      1,2,3,4       -

    Dequeue()->1      2,3,4         -
    Dequeue()->2      3,4           -
    Dequeue()->3      4             -
    Dequeue()->4      -             -

The time complexity is amortized O(1) because each element we put on the queue is only part of a reversal once. Unfortunately with immutable queues amortized complexity doesn't work so well, since after you do an operation the old version of the data structure is still there. So it could be the case that somebody dequeues repeatedly on a queue with an empty front, causing the expensive reversal operation to happen multiple times. There are ways around that, described in [Chris Okasaki's thesis](http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf). Getting O(1) complexity even if older versions can be used multiple times makes the data structure more complicated and costs us in terms of raw speed, so I will not do that.

Here's the full code:

{% highlight csharp %}
struct DoubleStackQueue<T>
{
    public struct Queue
    {
        NullLinkedListStack<T>.Stack front;
        NullLinkedListStack<T>.Stack back;

        public bool IsEmpty { get { return front.IsEmpty && back.IsEmpty;  } }

        public Queue Enqueue(T x)
        {
            return new Queue { front = front, back = back.Push(x) };
        }

        public Queue Dequeue(out T x)
        {
            if(front.IsEmpty) 
            {
                while(!back.IsEmpty){
                    T item;
                    back = back.Pop(out item);
                    front = front.Push(item);
                }
            }
            return new Queue { front = front.Pop(out x), back = back };
        }
    }

    public static Queue Empty = new Queue();
}
{% endhighlight %}

Can we optimize this? Yes we can: at the moment when we reverse the `back` stack, there is no reason to put them into `front` as a linked list. Since we are traversing the entire `back` stack anyway, we may as well store `front` efficiently in a contiguous array. Then when we Dequeue an item, we simply decrement a counter instead of copying the entire array. This keeps the GC from reclaiming the memory of elements that have already been dequeued until `front` is completely empty, however. Here is the full code:

{% highlight csharp %}
struct StackArrayQueue<T>
{
    public struct Queue
    {
        int count;
        List<T> front;
        NullLinkedListStack<T>.Stack back;

        public bool IsEmpty { get { return count == 0 && back.IsEmpty; } }

        public Queue Enqueue(T x)
        {
            return new Queue { front = front, back = back.Push(x), count = count };
        }

        public Queue Dequeue(out T x)
        {
            if (count == 0)
            {
                var newFront = new List<T>();
                var newBack = back;
                while (!newBack.IsEmpty)
                {
                    T item;
                    newBack = newBack.Pop(out item);
                    newFront.Add(item);
                }
                var newCount = newFront.Count - 1;
                x = newFront[newCount];
                return new Queue { front = newFront, back = newBack, count = newCount };
            }
            else
            {
                x = front[count - 1];
                return new Queue { front = front, back = back, count = count - 1 };
            }
        }
    }

    public static Queue Empty = new Queue();
}
{% endhighlight %}

### Benchmarks ###

For queues I use the same benchmark as for stacks, except instead of pushing and popping at the front, we enqueue and dequeue at opposite ends.

Here are the queue results:

<table border="1">
<tr><th>Implementation</th><th>Time</th><th>Memory</th></tr>
<tr><td>Collections.ImmutableQueue</td><td>2570 ms</td><td>63999944 bytes</td></tr>
<tr><td>DoubleStackQueue</td><td>1266 ms</td><td>63999904 bytes</td></tr>
<tr><td>StackArrayQueue</td><td>917 ms</td><td>36194368 bytes</td></tr>
</table>

The StackArrayQueue is clearly superior to the others: it is far faster and uses far less memory.