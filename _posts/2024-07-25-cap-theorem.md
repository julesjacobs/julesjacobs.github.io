---
title: "The CAP theorem"
---

The CAP "theorem" (previously "Brewer's conjecture" until it was "[proved](https://dl.acm.org/doi/abs/10.1145/564585.564601)" -- 2972 citations according to Google Scholar) is the trivial observation that if you have a database implemented by two servers, and the connection between the two servers is lost, then if you write to server 1 and then read from server 2, you won’t see the newly written value. The end.