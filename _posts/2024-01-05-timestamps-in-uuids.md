---
title: "Timestamps in UUIDs"
---

Using [timestamps as part of UUIDs](https://www.ietf.org/archive/id/draft-peabody-dispatch-new-uuid-format-01.html
) has advantages:

1. No need to store creation time separately
2. UUIDs sort by creation time
3. When using B-trees, we get temporal locality

However, is there a collision cost?

Consider these two UUID formats, where $$K > k$$:

* Option 1: $$K$$ random bits.
* Option 2: Timestamp with second precision + $$k$$ extra random bits

Assume that we get N events every second. With option 1, the collision risk increases linearly with time, because each new UUID can collide with any of the previous ones. With option 2, the collision risk is constant, because each new UUID can only collide with other UUIDs from the same second.

It might therefore seem that option 2 is better, but is it? Let's calculate.

## Option 1

Collision rate after $$M$$ seconds:
  - We have $$NM$$ previous events
  - Probability that the next event collides with any of the previous ones is $$NM/2^K$$
  - Collision rate $$\approx N^2M/2^K$$

## Option 2

Collision rate is constant:
  - Probability that two given events collide is $$1/2^k$$
  - Collision rate $$\approx N^2/2^{k+1}$$

## Conclusion

For which $M$ does Option 2 start to be better than Option 1?
We solve $$N^2M/2^K = N^2/2^{k+1}$$, so

$$ M = 2^{K-k-1} $$

If we use the $K-k$ bits for the timestamp, then Option 2 is better only after half timestamp range is exhausted!
Perhaps not surprising in hindsight.

Conclusion: put the timestamp in the UUID to reap the aforementioned advantages, but don't don't expect an improvement in collision rate.
In fact, given the non-uniformity of events in practice, the collision rate might be a bit worse, but with 128 bits, it's not a problem.
