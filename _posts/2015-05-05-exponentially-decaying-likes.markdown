---
layout: post
title:  "Determining hot items with exponentially decaying likes"
date:   2015-05-06 13:00:40
categories: 
---

Many sites want to determine recently popular items, for example:

* Posts on Facebook that have been liked a lot recently
* Hashtags on Twitter that have been mentioned a lot recently
* Producs on Amazon that have been bought a lot recently
* Posts on reddit that have been commented on a lot recently
* Posts on Hacker News that have been upvoted a lot recently
* Articles on a newspaper site that have been read a lot recently

The general trend is that we have a set of items (facebook posts, hashtags, products, etc.) and each item can receive generalized 'likes' (facebook likes, hashtag mentions, product purchases, etc.), and we want to determine those items that have recently received a lot of those likes. In this post I'm going to describe such a method with appealing theoretical and practical properties. Here's a demo that you can play with:

<style>
#wraptable {
	border: 1px solid grey;
	margin: 20px;
}
#decay { 
	width: 500px; 
	margin: 10px;
}
#decay td { padding: 3px 5px 3px 5px; }
#decay td div { background: #F17022; float: left; border: 1px 0px 1px 0px; }
#decay td div:nth-child(even) { background: #62C2CC; }
#decay tr td:nth-child(3) { width: 300px; }
</style>

<div id="wraptable"><table id="decay"></table></div>

<script src="http://d3js.org/d3.v3.min.js" charset="utf-8"></script>

<script>

var rate = 1/30000;
var names = ["Apples", "Pears", "Bananas", "Oranges", "Kiwis"];
var likes = names.map(function(s){ return []; });
var scores = names.map(function(s){ return 0; });

function decay(age){ return Math.exp(-rate*age); }
function sum(xs){ return xs.reduce(function(a,b){ return a+b; }); }
function decays(ages){ return ages.map(decay); }
function score(ages){ return sum(decays(ages)); }
function getAges(t,i){
	return likes[i].map(function(l){ return t-l; });
}

function like(i) {
	var time = new Date().getTime();
	likes[i].push(time);
	scores[i] = updatedScore(scores[i], time);
}

function updatedScore(z,t) {
	var u = Math.max(z,rate*t);
	var v = Math.min(z,rate*t);
	return u + Math.log1p(Math.exp(v-u))
}


function render() {
	var x = d3.scale.linear()
			  .domain([0,10])
			  .range([0,200]);

	var t = new Date().getTime();
	var data = names.map(function(name, i){ return {"name": name, "likes": decays(getAges(t,i)), "score": scores[i]}; });

	var tr = d3.select("#decay")
	  .selectAll("tr")
	  	.data(data);
	
	var newtr = tr.enter().append("tr");
	newtr.append("td");
	newtr.append("td").append("button").text("like").on("click", function(e,i){ like(i); });
	newtr.append("td");
	newtr.append("td");

	tr.select("td:nth-child(1)").text(function(row){ return row.name; });

	var likebars = tr.select("td:nth-child(3)").selectAll("div").data(function(row){return row.likes;});
	likebars.enter().append("div").html("&nbsp;")
	likebars.style("width", function(s) { return x(s) + "px"; });

	tr.select("td:nth-child(4)").text(function(row){ return row.score; });
	window.requestAnimationFrame(render);
}

var lastInit = 0;
function init() {
	var t = new Date().getTime();
	if(t - lastInit > 30000){
		lastInit = t;
		names.forEach(function(n,j) {
			for(var i=0; i < 10; i++) { 
				if(Math.random() < 0.5) {
					like(j);
				}
			}
		});
	}
}

init();
render();

window.onfocus = init;
</script>

The rest of this post is about why exponential decay is a good way to score hot items, and how to implement that very efficiently in just a couple of lines of code. If you are not interested in the math you can skip straight to the code section below.

## Why not sort items by number of likes received in the last hour? ##

At first sight it seems like a good idea to pick a time window, say one hour, filter out all the likes that happened in that time window, and then sum up all those likes for each item to obtain a score. Then we sort all items by score and pick the top scoring items. This does work but it has a couple of disadvantages. What if item A got 100 likes the last hour, and 0 likes in the hour before that, but item B got 99 likes last hour, and 100 likes in the hour before that. It does not make much sense to rank A higher than B, but due to the sharp cut-off we value that 1 like higher than those 100. Similarly, what if item A got 100 likes spread around the last hour, but item B got 99 likes in the last 5 minutes? Surely item B is more 'hot' than A. We would like to gradually decrease the influence of likes that are further in the past.

The second issue with this method is that it's inconvenient to implement efficiently. Doing a query for all likes in the last hour and summing them up could be very time consuming. The efficient way to implement it is to maintain a running score for each item. Every time it gets liked we increment the score, and every time a like gets older than an hour we decrement the score. This is inconvenient and does not fit well within the abilities of conventional databases.

## Why not apply a penalty based on item age? ##

Some sites apply a penalty based on the age of an item (as opposed to the age of the like). Hacker news for example uses a formula like `score = votes / age^1.8`. This also has an ineffiency problem: we have to continually recompute the score of every item to determine the current ranking. This could be fixed by picking a score formula of the form `score = f(votes) + g(time)` where `g` is some function of the time that an item was created/posted. Instead of penalizing items based on age, we simply give a boost to newer items. Reddit uses this approach. It has a major advantage: we only need to update the score in response to new votes, and not continually over time. Furthermore, we can simply store the score as an indexed column or attribute in our database, and then we can efficiently retrieve the top N items by score.

Unfortunately this method also has a disadvantage. If you think about it then the hotness of an item should only depend on when it was voted on, not on when it was created. A book on Amazon could suddenly become a popular purchase, even though it may have been written a long time ago. On Hacker News you are at a disadvantage if you post an item during the night when there are fewer people to vote compared to posting during the day (in California time). Do this thought experiment: suppose that Hacker News got zero visitors during the night, and suppose that post A was posted at the start of the night, and post B was posted at the beginning of the next morning. Neither post would get any votes during the night, so in the morning both are at zero votes. Then people start waking up and start voting, and suppose that both A and B get the same number of votes. Because A is older it gets a bigger penalty with `votes / age^1.8`: each of its votes counts for much less than B's votes. So a post that is posted during a quiet time has little chance to rank high simply because of the time at which it was posted. The solution is to determine the score by vote age, not by post age.

## Desiderata ##

Can we do better? Let's list a couple of properties that we would like to have:

1. The score of an item is the sum of value of its likes.
2. The value of a like is determined by its age: the value of a like decreases over time.
3. Relative ordering of items only changes in response to likes.

Note that in thist post I'm only considering upvotes/likes/purchases/pageviews, and no downvotes. I hope these properties sound sensible to you. I've already motivated 1 and 2 in the previous section, and 3 is reasonable as well: if A is hotter than B at this moment, and there are no new likes, then A is still hotter than B one minute from now. The passage of time alone can affect the score, but not the relative ordering of items.

Exponentially decaying like values satisfy these requirements. Exponential decay means that for a given interval of time the value shrinks by a constant factor. One option is that the value of each like gets cut in half every hour. After two hours it is at one fourth, and after three hours at one eighth. This happens smoothly: after 30 minutes the value of a like decreases by roughly 30%, and each minute the value of a like decreases by roughly 1%. In mathematical terms the value of a like is e<sup>-at</sup>, where `a` is the decay rate and `t` is its age. If we want to find the hot items in the last hour we would pick a decay rate of roughly 1/n where n is the number of milliseconds in one hour (if we are measuring time in milliseconds).

It turns out that not only does exponential decay satisfy those 3 properties, it is also the <i>only</i> solution that satisfies all 3 properties. Proving this is left as an excercise for the mathematically inclined reader ;-)

## Efficient implementation ##

As you can see in the demo this is not particularly efficient if we implement it directly. We need to continually update the like values of all likes. But there's hope: the relative ordering of items only changes in response to likes. So we could keep the scores constant, and only update all of them when a new like comes in. This is still inefficient however: the total number of items could be huge, and updating <i>all</i> of them each time <i>one</i> item gets liked is too much work.

### Math to the rescue ###

Recall that the value of a like is e<sup>-at</sup> where t is the age, i.e. t = t<sub>now</sub> - t<sub>like</sub>, where t<sub>like</sub> is the time when the item got liked. Plugging this in we get e<sup>-at</sup> = e<sup>-a(t<sub>now</sub> - t<sub>like</sub>)</sup> = e<sup>-at<sub>now</sub></sup> e<sup>at<sub>like</sub></sup>. Here is the first idea: divide all like values by e<sup>-at<sub>now</sub></sup>. Since we are didiving all values by the same amount it does not affect the relative ranking. After doing this the value of a like is simply e<sup>at<sub>like</sub></sup>, which is independent of time t<sub>now</sub>! Since the score is the sum of those values, we have a score that only needs to be updated in response to new likes to that particular item, and no longer needs to be updated continuously as time passes. Yet it will give us exactly the same ranking as exponentially decaying likes. Every time a new like comes in, increment the score s of the item that is being liked: s := s + e<sup>at<sub>like</sub></sup>, where t<sub>like</sub> is the time that the like happened. To produce a ranking we take the top N items by score. This is an operation that any database worth its salt can do very efficiently if the score column is indexed.

Although the value of a given like is not changing with time any more, likes that were performed at different times do have different values. In fact as time goes on the value of new likes is increasing exponentially. This is a problem because we need to store larger and larger scores, and since the growth is exponential we will quickly exhaust any bit width. We can fix this by working with the log of the score z = log(s). Although s is increasing exponentially, z is increasing only linearly. So with a sufficient but small bit width it will take a VERY long time before we run out of bits.

We need to figure out how to update z instead of incrementing s. Since s = e<sup>z</sup>, we have s := s + e<sup>at<sub>like</sub></sup> = e^z + e<sup>at<sub>like</sub></sup>. Since z = log(s) we need to use the formula z := log(e<sup>z</sup> + e<sup>at<sub>like</sub></sup>) to update z. Although the number z that we store is now small, the intermediates e<sup>z</sup> and e<sup>at<sub>like</sub></sup> are still big. We can fix this by rewriting as follows. Let u = max(z,at<sub>like</sub>) and v = min(z,at<sub>like</sub>). Then e<sup>z</sup> + e<sup>at<sub>like</sub></sup> = e<sup>u</sup> + e<sup>v</sup> = e<sup>u</sup>(1 + e<sup>v - u</sup>). If we substitute this into the formula for z we get z := log(e<sup>u</sup>(1 + e<sup>v - u</sup>)) = u + log(1 + e<sup>v - u</sup>). Since u is the max and v is the min, v - u is less than 0, so e<sup>v - u</sup> is a small number. We no longer have any overflow issues!

We do still have precision issues: e<sup>v - u</sup> is a small number, so when we add 1 to it we could lose a lot of precision. Fortunately there exists a solution for this. Instead of using the ordinary log(1+x) function, we use the function log1p(x) = log(1+x), but unlike log(1+x), log1p(x) does not lose precision for small x. Many languages have this function in their standard library, including Javascript which I used to implement the demo.

How many bits of precision do we need? The problematic case is when t<sub>like</sub> is large, and we have many likes in a short period of time. Each successive like adds e<sup>t<sub>like</sub></sup> to the s score, but since we are working with z = log(s) each successive like adds a smaller and smaller value to z. It turns out that the n-th like in quick succession adds approximately 1/n to z (Another exercise for the reader. Hint: log(n+1) - log(n) = 1/n + O(1/n^2)). Such a value can be accurately added to a value of size z with O(log(z) + log(n)) bits of precision. Since z is roughly of size at<sub>like</sub> this gives us very good scaling. With each additional bit we can either run the system twice as long, or be able to accurately represent twice as many votes. With a reasonable decay rate such as decaying by half each hour, we will not exhaust the space of double precision floating point any time soon (a double float has 52 bits of precision, so if we take 5 bits for safety, and a maximum of 1 million instantaneous likes per item, we will be able to run the system roughly until the year 18,000). Note that votes spread out over time are no issue. If you want a very tiny decay rate and very high number of votes in a short timeframe you may need to go to 64 or 128 bit fixed point, then you can sustain a trillion instantaneous votes until after the heat death of the universe.

You can see the math in action in the demo: the sort order of the static scores is always the same as the sort order of the decaying likes.

### Intuitive interpretation of the z score ###

There is a cute interpretation of these scores. When an item gets a single vote at time `t`, the score is `at`. When it gets a second vote shortly after that, its score will be incremented by a small amount: `at + ɛ`. At some future point in time a single vote would be worth `at + ɛ` on its own. So the z score of an item can be interpreted as the point in time when a single vote would give that much score. Multiple votes are like a single future vote, and the system keeps track of scores by combining votes into a single future vote.

## The code ##

Here is the code in Javascript:

{% highlight javascript %}
function updatedScore(z,t) {
    var u = Math.max(z,rate*t);
    var v = Math.min(z,rate*t);
    return u + Math.log1p(Math.exp(v-u))
}
{% endhighlight %}

This function receives the old score z and the time of the like t as input, and computes the new z score. It also makes use of the `rate` variable, which controls how fast the decay is. A higher rate results in a faster decay. This function should be used in the following way:

{% highlight javascript %}
// update the score in response to an incoming like
post.score = updatedScore(post.score, new Date().getTime())
{% endhighlight %}

`new Date().getTime()` is Javascript's way of getting the time in milliseconds since the Unix epoch. In the demo you can see the score numbers.

The decay rate that you pick depends what your time window for hotness is. Do you want to find the hot items roughly in the last minute, hour, day, or even year? If your timespan is t, then you would pick a decay rate of 1/t. For example, if you wanted the hot items in the last hour, you would pick `rate = 1/3.6e6` since there are 3.6 million milliseconds in an hour. This would decay the values by a factor of 1/e every hour, which is approximately 0.37. If you prefer to work with factors of 1/2, you multiply your rate by log(2). So if you wanted a decay by half every hour, you would pick `rate = log(2) * 1/3.6e6`. If you wanted to be able to both find the hot items of the last hour and the hot items of the last week you would keep 2 separate score columns, each computed with a different decay rate.

## Conclusion ##

Although the analysis is a bit involved, the resulting code is very simple. What we have is a way to find hot items that:

1. Does not have a sharp cut-off: instead of completely ignoring likes older than a cut-off, and valuing likes within the cut-off exactly the same, we smoothly value older likes less.
2. Scores only based on the age of each individual like, not based on the age of the item.
3. Is very efficient: we only update the score of one item in response to a like of that item, and we can use existing databases to retrieve the top N scoring items.
4. Is easy to implement: the core code is just 3 lines.

I would be happy to hear about your experience if you decide to use this method.