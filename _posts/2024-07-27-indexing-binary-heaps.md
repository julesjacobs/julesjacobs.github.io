---
title: "Indexing Binary Heaps"
---

Binary heaps can be stored in a flat array:

```
heap:   [1,  2,3,   4,5,6,7,    8,9,10,11,12,13,14,15,   ...]
parent:      1 1    2 2 3 3     4 4 5  5  6  6  7  7 
```

The root is `1`, which has children `2,3`. The `2` has children `4,5`, etc.
The parent of each element is written below it.


Our three questions of today are:
1. How do we compute the index of the parent of node i?
2. How do we compute the index of the left child of node i?
3. How do we compute the index of the right child of node i?

[Wikipedia](https://en.wikipedia.org/wiki/Binary_heap) gives us the answer, but Wikipedia's derivation of the formulas is fairly complex and requires a bit of mathematical calculation.

**We will derive these formulas without any calculation. You will immediately understand why the formulas work:**


Although 0-based indexing is *usually* better, 1-based indexing is better in this particular situation. Let's write out the 1-based heap indices in binary:

```
heap:   [1,  10,11,   100,101,110,111,   1000,1001,1010,1011,1100,1101,1110,1111,   ...]
parent:      1  1     10  10  11  11     100  100  101  101  110  110  111  111
```
As you can see, each level consists of numbers `10..00` through `111..11`.
Finding the parent of an index simply amounts to removing the last digit! 
Finding the left child amounts to adding a 0 at the end, and finding the right child amounts to adding a 1 at the end:

```
parent(i) = i >> 1
left(i) = (i << 1) + 0
right(i) = (i << 1) + 1
```

That's it! When you turn these into 0-based indices, you indeed get the formulas on Wikipedia, but we got them without any calculation :)