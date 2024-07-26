---
title: "The CAP theorem"
---

The CAP "theorem" states that if you have a database implemented by two servers, and the connection between the two servers is lost, then if you write to server 1 and then read from server 2, you won’t see the newly written value. The end.