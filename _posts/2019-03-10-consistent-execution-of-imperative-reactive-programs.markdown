---
title: "Consistent execution of imperative reactive programs"
date:   2019-03-10 22:00:00
---

This is a comment in response to [Sandro Magi's comments on FRP and S.js](http://julesjacobs.github.io/2018/02/22/hooks-bring-react-closer-to-frp.html#comment-4358285816), turned into a post. S.js lets you create data signals with `x = S.data(initial value)`, read them with `x()` and write to them with `x(value)`. It also lets you create computations with `S(() => {...})`. When a signal is read in a computation, the computation is re-run whenever the signal's value changes. When you write a value to a signal, reading from the signal doesn't immediately return the new value. Instead, time progresses in ticks, and updates from tick n are only visible in tick n+1. Could we change that behaviour so that reading from a signal always returns its most recent value?

This creates a scheduling problem when the computation imperatively updates other signals, because the order in which we run computations may lead to different results. We could try to run computations in an order such that computations that write to a signal are executed before computations that read a signal. This could be done by running the computations in any order, keepping track of which computations read and write each signal, and if a computation A reads from `x` and B then writes to `x`, we abort. Then we repeat, now scheduling the computations that write to a signal before the computations that read from it.

I haven't thought about this too deeply, but one danger is that this process will run in circles even if a consistent schedule exists, or at least take exponentially many restarts to find a consistent schedule. Another issue is that sometimes multiple consistent schedules exist that lead to different outcomes. Imagine a computation A that reads from x and writes y=1 if x==0, and a computation B that reads from y and writes x=1 if y==0. If x=0 and y=0 initially, then both orders AB and BA give a consistent schedule, but lead to different outcomes.

Is an "imperative reactive" programming model therefore doomed? I don't know.

This is not actually how you write S.js code, by the way. A computation `S(() => {...})` returns a signal based on the value that the lambda returns. Unlike when imperatively updating some existing signal, this allows S.js to understand the dataflow graph ahead of time, and schedule updates in the correct order while guaranteeing that each computation is only run once per tick. So the issue that signal reads return the old value usually doesn't come up.