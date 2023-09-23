---
title: "Deep learning is maximum likelihood"
---

The talk of deep learning, with complicated sounding terms such as "cross entropy", "Kullback-Leibler divergence", "Kolmogorov complexity" has me a bit puzzled. I think it's important to not get befuddled by fancy sounding terms, and remember that deep learning is just good old maximum likelihood estimation, as described by Fisher 100 years ago. In this post, I'll try to explain what that means.

## The kind of deep learning I'm talking about

The kind of deep learning I'm talking about is _supervised classification_: Given a set of training examples $$(x_1, y_1), \ldots, (x_n, y_n)$$ where $$x_i$$ is a vector of input features and $$y_i$$ is an output label, we want to learn a classifier function $$f(x)$$ that predicts the label $$y$$ for a new example $$x$$. Lots of the exciting kinds of deep learning fit into this framework. For instance, in image classification, the features $$x$$ are the pixels of the image, and the labels $$y$$ are the categories of the image (e.g., "cat", "dog", "car", etc.). In large language models for next-word prediction (such as the model at the base of ChatGPT), the input $$x$$ is a sequence of words, and the prediction $$y$$ is the next word that could follow the sequence.

## Predict probabilities, not labels

When we're talking about predicting, we're talking about _probability_. For instance, if we're trying to predict the next word in a sentence "The dog bit the", we don't just want to predict the most likely word, we want to predict the probabilities all of possible next words: "I'm 90% sure that the next word is 'cat'". In other words, we want to predict a _probability distribution_ over the possible labels $$y$$ given the features $$x$$. We have a finite number of possible labels, so we can represent this probability distribution as a vector $$f(x)$$ of probabilities, where $$f(x)_\ell$$ is the probability of label $$\ell$$.

So the setup is that we're trying to find a function in some class

$$ f_\theta : \text{features} \rightarrow \text{probability distribution over labels} $$

where $$\theta$$ is a vector of parameters that we want to learn. For instance, in a neural network, $$\theta$$ is the set of weights in the network. The function $$f_\theta(x)$$ is the computation of the network itself: it takes in the features $$x$$ and outputs a probability distribution over labels by doing some big complicated computation involving the weights $$\theta$$ and the features $$x$$.

## Maximum likelihood estimation

Okay, so how do we learn the parameters $$\theta$$? Well, we have our training examples $$(x_1, y_1), \ldots, (x_n, y_n)$$. Maximum likelihood says:

> Choose the parameters $$\theta$$ that maximize the predicted probability of the training answers.

We can view $$f_\theta$$ as a generative model: given some features $$x$$, we generate a label $$y$$ according to the probability distribution $$f_\theta(x)$$. Like how ChatGPT generates the next word. Maximum likelihood says that we should choose the parameters $$\theta$$ that make the training examples most likely to be generated. Makes sense, right? Rather than choosing some $$\theta$$ that makes $f_\theta$$ generate some totally random output, we should choose $$\theta$$ that makes $$f_\theta$$ generate the training input-output examples.

The math here is exceedingly simple. The probability of the training set is just the product of the probabilities of each training example:

$$ \text{probability of the training set} = \prod_{i=1}^n f_\theta(x_i)_{y_i} $$

## Two slight complications

There are two slight complications here:

1. Numerically, multiplying a whole bunch of probabilities together can be a bad idea, because the product can get very small.
2. The probability distribution $$f_\theta(x)$$ must actually _be_ a probability distribution: the probabilities must all be numbers between 0 and 1, and they must sum to 1.

There are standard ways to deal with both of these problems that are as old as statistics itself, and they're both very simple.

You can get around the first problem by taking the log of the probabilities and adding them together instead:

$$\log(\text{probability of the training set}) = \sum_{i=1}^n \log f_\theta(x_i)_{y_i} $$

This is totally standard and always done for maximum likelihood estimation.

You can get around the second problem by using another standard trick to turn any old vector into a probability distribution: first make all elements non-negative by exponentiating them, and then divide by the sum to normalize it to $$1$$. If we have any old function $$g_\theta(x)$$, we can turn it into a probability distribution by defining

$$f_\theta(x)_\ell = \frac{e^{g_\theta(x)_\ell}}{\sum_{\ell'} e^{g_\theta(x)_{\ell'}}}$$

This $$f$$ outputs a valid probability distribution regardless of what the function $$g$$ does. This trick that is at least as old as logistic regression, which is the special case when $$g$$ is a linear function.

If we substitute this $$f_\theta(x)_\ell$$ into the log probability equation above, we get

$$ \log(\text{probability of the training set}) = \sum_{i=1}^n \left[ g_\theta(x_i)_{y_i} - \log \sum_\ell e^{g_\theta(x_i)_\ell} \right] $$

And of course, if you so desire, you can also put a minus sign in front of the whole thing and call it a _loss function_, and minimize instead of maximize:

$$ \text{loss} = -\sum_{i=1}^n \left[ g_\theta(x_i)_{y_i} - \log \sum_\ell e^{g_\theta(x_i)_\ell} \right] $$

If we have only two labels this turns into the more familiar binary cross entropy loss:

$$ \text{loss} = -\sum_{i=1}^n \left[ y_i \log f_\theta(x_i) + (1-y_i) \log (1 - f_\theta(x_i)) \right] $$

## So why is everyone talking about cross entropies and Kullback-Leibler divergences?

I don't know. It is true that if you take the KL divergence $$D_{KL}(p,q)$$ and make $$p$$ be the probability distribution that puts all mass on the true example $$y_i$$,

$$ p_\ell = \begin{cases} 1 & \text{if } \ell = y_i \\ 0 & \text{otherwise} \end{cases} $$

then the KL divergence is simply

$$ D_{KL}(p,q) = -\log q_{y_i} $$

In other words, **taking such a KL divergence with a distribution that puts all probability on the true example is just a very roundabout way of taking the log probability of the true example**. But I don't see why you would want to do that. It seems like a lot of extra complication for no reason.

Similarly, the cross entropy $$H(p, q)$$ is just

$$ H(p,q) = H(p) + D_{KL}(p,q)$$

where $$H(p)$$ is the entropy of $$p$$. But if $$p$$ assigns all probability mass to the true example, then the entropy $$H(p)$$ is just zero. So again, taking this cross entropy is just a very roundabout way of the log probability of the true example.

There's one exception to this, and that is if your training data is itself given as a probability distribution. That is, you have data set with images _labeled_ with "30% chance this is a cat, 70% chance this is a dog". If you have _that_, then sure, KL divergence is the natural way to go.

## Log probabilities and entropy

There **is** a **good** non-numerical reason to talk about entropy and log probabilities, and that is that they are additive rather than multiplicative. That is, if you have two independent probabilities $$p$$ and $$q$$, then the probability of both of them happening is $$p \cdot q$$, but the log probability of both of them happening is $$\log p + \log q$$. In other words, log probabilities let you combine independent effects with addition.

Logistic regression exploits this: we combine the effects of different features by taking a linear combination and interpreting that as a log probability.
This rests on the assumption that the different features are independent signals. Note that we're *not* assuming that the features are statistically independent; only that they are independent *signals* for the output we're trying to predict.

There's a similar effect in the last layer of a neural network, where we take a linear combination of the outputs of the previous layer and interpret that as a log probability. Gradient descent now doesn't need to do the hard work of figuring out how to combine independent signals; the network does that for us. Gradient descent just needs to provide the signals and their weights.

## Compression and bits

There's another good reason to talk about entropy and log probabilities, and that is that they are related to compression. If you have a probability distribution $$p$$, then an optimal encoder will be able to encode each element $$\ell$$ of the distribution using $$-\log_2 p_\ell$$ bits. This is the famous Shannon source coding theorem.

It is sometimes said that LLMs are trying to compress the training set. That this is equivalent to maximum likelihood is easily seen from the preceding formula: if we maximize the probability $$p_\ell$$, then clearly we minimize the number of bits $$-\log_2 p_\ell$$ needed to encode $$\ell$$.

I'm not sure how useful this is, though. It seems to me no different from saying that LLMs are trying to maximize the likelihood of the training set. It's just a different way of saying the same thing. In particular, upon reflection, *it has nothing to do with the KL divergence or cross entropy derivations of the loss function*, despite the fact that the KL divergence and cross entropy are also related to compression. You *can* derive the loss function from compression, but that's exactly the derivation I gave above, and it has nothing to do with the KL divergence or cross entropy derivations that you often see.

It may be *psychologically* useful to think in terms of bits instead of probabilities, in some cases. For instance, we can say that a LLM compressed a given test set to an average of 2 bits per word. Equivalently, we can say that on average, the LLM assigned a probability of $$2^{-2} = 0.25$$ to the correct next word.

Similarly, if we're doing simple logistic regression for spam/genuine classification, we can say that the presence of the word "viagra" is worth 5 bits of evidence for spam. Equivalently, we can say that the presence of the word "viagra" multiplies the probability of genuine by $$2^{-5} = 0.03125$$.

Compression and entropy are different ways of talking about probabilities, but may be useful tools of thought.

## Conclusion

Deep learning is just maximum likelihood estimation. This isn't a new insight; obviously the experts are well aware of this. But the fancy sounding terms keep popping up, hence this post.