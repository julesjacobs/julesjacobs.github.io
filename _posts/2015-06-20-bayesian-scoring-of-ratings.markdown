---
layout: post
title:  "Bayesian ranking of items with up and downvotes or 5 star ratings"
date:   2015-06-20 0:30:40
categories: 
---

[[
Bayesian ranking/ordering/sorting?
Move Evan Miller reference to the end?
Use popularity p = probability p.
Pictures of beta distribution.
Loss function focusing on 1 visitor.
]]

Evan Miller wrote a great article [How Not To Sort By Average Rating](http://www.evanmiller.org/how-not-to-sort-by-average-rating.html). He shows that simple formulas like `score = upvotes - downvotes` or `score = upvotes / (upvotes + downvotes)` don't work. He proposes to use the lower bound of the Wilson score confidence interval. The formula is complicated and somewhat of a hack: there isn't a clear statistical justification for it (as is usual for frequentist methods). Later he wrote a follow-up about a Bayesian approach to fix the hack [Bayesian Average Ratings](http://www.evanmiller.org/bayesian-average-ratings.html). That approach has a much clearer statistical justification: he only assumes a Beta distribution for the prior (which is the natural choice for this problem), and he assumes a utility function. The utility function he assumes works as follows:

> Call this “loss multiple” L. Five seems like a reasonable number to me, but you can play around with your own choice. A loss multiple of five says that it's five times worse to rank an item too high on a list than to rank it too low. In this way, we'll avoid placing an item very high on list unless we have a relatively strong belief that its average rating is high.

Unfortunately this utility function makes the computation relatively complicated, since we need the inverse incomplete beta function to compute the ranking. Furthermore, as I'll show shortly, this utility function is not actually as natural as it seems at first sight. In this post we'll explore an alternative method with the following advantages:

1. Simpler formulas
2. Optimized for what we actually want to achieve with a ranking
3. Easily generalized to more than 2 vote options, such as 5 star rating

## The stats ##

Let's first consider an individual item. Some people will give it a upvote, others will give it a downvote. Let the popularity `p` be the fraction of people that would give the item a upvote. When a new item is posted to the site we don't have any votes yet, so we don't know what `p` is going to be, but as more votes come in it will become clearer. At 300 upvotes and 100 downvotes it's clear that `p` is going to be close to `300 / (300 + 100) = 1/4`. When we have 3 upvotes and 1 downvote it's less clear. This is what Bayesianism is all about: we quantify the uncertainty by assuming a prior probability distribution over `p`. The standard probability distribution to use is the [Beta distribution](https://en.wikipedia.org/?title=Beta_distribution), `Beta(a,b)`. A beta prior is equivalent to assigning "pretend votes" to each new item. Instead of starting out with 0 upvotes and 0 downvotes, we start out with `a` upvotes and `b` downvotes. If we expect that most items are bad, we could start with 3 upvotes and 10 downvotes. After getting `u` real upvotes, and `d` real downvotes the posterior distribution is `Beta(a+u, b+d)`.

## The ranking

Let's consider a ranking of several items. Why would we prefer one ranking over another? We would like to rank good items, the items with lots of upvotes and few downvotes, at the top. But why? The reason is that people are more likely to look at the top of the ranking than at the bottom, and we want to show people items that they will like. Let's be a bit more precise. If we display a ranking, then 300 people will look at the top item, 180 will look at the second item, 130 at the third item, etcetera. The point is that the number of people who look at the n-th item decreases. Now it's clear why we rank good items higher than bad ones: because we would like to maximize the number of people who look at good items, and minimize the number of people who look at bad items. Because more people look at the items at the top, we want to put the good items there.

With can formalize this with a utility function. Each time a person looks at an item they like we get a bit of happiness or [utility](https://en.wikipedia.org/wiki/Utility#Utility_functions) `X` and each time somebody looks at an item they don't like we get a bit of unhappiness or negative utility `Y`. We could choose `X = +4` utility points for somebody looking at an item they like, and `Y = -9` utility points for somebody looking at an item they dislike. We want to rank the items in such a way that the expected utility is maximized.

Which item should we put at the top spot to maximize the expected utility? Let `p` be the popularity of the item that we would put at the top spot. If `n` people look at the top spot, then `n*p` people will like it and `n*(1-p)` people will dislike it, so the expected utility is `E[n*p*X + n*(1-p)*Y]`. Some calculating gives:

    E[n*P*X + n*(1-p)*Y] = n*X*E[p] + n*Y*E[1-p] = n*X*E[p] + n*Y*(1-E[p])
	
The only term that depends on the item is `E[p]`, the expected popularity of the item. So if we want to maximize the expected utility we get out of the top spot, we should put the item with maximum *expected* popularity there. The same goes for the other spots. We conclude:

> To maximize the expected utility, sort the items by expected popularity.

For the `p ~ Beta(u,d)` distribution the expected popularity `score = E[p] = u/(u+d)`. This might be a bit surprising, because this is simply `score = upvotes / (upvotes + downvotes)`, and Evan Miller showed that this does not produce a desirable ranking. But wait, because we started with a beta prior with `a` pretend upvotes and `b` pretend downvotes, this is not quite the same. We've got a `p ~ Beta(a+u, b+d)` distribution. The score formula that we end up with is:

    score = E[p] = (a+u) / (a+u + b+d)

In summary, when you have a list of items each with some number of upvotes `u` and downvotes `d`, pick a prior `a` upvotes and `b` downvotes and sort the items by that score formula. Note that the utilities `X` and `Y` have disappeared from the formula. It doesn't matter what they are, as long as `X` > `Y`, i.e. we like upvotes more than downvotes.

    pretend_upvotes = 4
	pretend_downvotes = 10
	
	def score(item_upvotes, item_downvotes):
	    upvotes = item_upvotes + pretend_upvotes
		downvotes = item_downvotes + pretend_downvotes
		return upvotes / float(upvotes + downvotes)
		
Perhaps surprisingly, adding pretend upvotes and downvotes not only fixes the problems of the `score = upvotes / (upvotes + downvotes)` in practice, but as we saw also has a far stronger statistical justfication than Evan Miller's original frequentist and bayesian methods. It's the optimal ranking given only the following assumptions:

1. The popularity of an item has a `Beta(a,b)` prior (Evan Miller uses this assumption too)
2. Higher ranked items get more views.
3. We want to maximize the expected number of times somebody views an item they would upvote, and minimize the expected number of times somebody views an item they would downvote.

## Ranking n-star ratings

Besides simplicity and statistical justification you were also promised a method that generalizes to n-star ratings. Instead of upvote and downvote being the only options, now we have 0 stars, 1 star, 2 stars, 3 stars, 4 stars and 5 stars. Instead of a `Beta(a,b)` prior we now need a Diriclet `Dir(a,b,c,d,e,f)` prior, which is a generalization of the `Beta` distribution to more than 2 classes. Which values you pick here can be determined by trial an error and checking which ranking it produces:

    pretend_votes = [3,4,2,5,3,6]
	
Or simply assign 2 pretend votes to each possible star rating:

    pretend_votes = [2,2,2,2,2,2]
	
Note that nothing stops you from assigning a fractional number of pretend votes. A prior with 2.3 pretend votes is perfectly fine.

Instead of two utilities `X` for upvote and `Y` for downvote, we need one utility for each possible star rating. It would make sense to say that the utility of viewing an item that you would have rated with `k` stars is equal to `k`:

    utilities = [0,1,2,3,4,5]
	
But maybe in a hypothetical world if you vote 0 stars it means you *really* don't like it, and if you vote 5 stars you *really* like it. Then you'd use these utilities:

    utilities = [-30, 1, 2, 3, 4, 70]

As with the prior, fractional utilities are fine.

Computing the score is only a bit more complicated than before:

    def score(item_votes):
		votes = [iv+pv for (iv,pv) in zip(item_votes,pretend_votes)]
		return sum(v*u for (v,u) in zip(votes,utilities))/float(sum(votes))
		
That's all there's to it! You can also use this code for upvotes/downvotes. Simply use `utilities = [0, 1]` (or any `[X,Y]` with `X < Y`, for that matter), and you'll get the same ranking as before.