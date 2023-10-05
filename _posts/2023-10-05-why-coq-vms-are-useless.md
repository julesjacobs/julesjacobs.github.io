---
title: "Why Coq VMs are useless"
---

When you write an academic paper with associated proofs mechanized in the Coq proof assistant, these conferences often require or strongly encourage you to submit a virtual machine image containing your Coq development. In this post I'm going to explain why this is a bad idea. Take this with a grain of salt, because I've just spent 6 hours trying to get my Coq VM to work, and I'm still not done.

## Why do conferences require VMs?

There are several arguments for requiring VMs:

1. It's easier for the reviewers to check the proofs if they can just boot up the VM and run them.
2. The VM is a self-contained artifact that can be archived and referenced in the future.
3. The VM allows the reviewers to verify that the proofs are correct

I don't think any of these arguments hold up.

## It's easier for the reviewers

Having been an artifact reviewer myself, I strongly disagree. It's much easier to download a zip file and run `make` than to install the VM software of the day, figure out how that works, then download a several gigabyte VM image, boot it up, and figure out how to do the build process inside the VM. The reviewers who choose to review Coq artifacts are likely to be already familiar with Coq. Even if they are not familiar with Coq, it's still easier to install Coq than to install a VM. Using the VM is extra frustrating because it's unfamiliar, slow, and you often can't easily copy-paste or transfer files from the VM to your host machine. That's bad because the VM probably doesn't have your favorite text editor, and if you're using a different keyboard layout than the one configured in the VM, then you're going to have an extra bad time. I've resorted to logging into my email account from inside the VM and emailing myself the files I want to copy over, while looking at a picture of the QWERTY keyboard layout to figure out how to type my password.

## The VM is a self-contained artifact

This is true, but not useful. If somebody down the line wants to build on your code, they are not going to do so inside a VM; they will want to build it on their actual computer. Therefore, effort of the authors and the reviewers is better spent on making that easy. If the reviewers want to use their own VM, they are still free to do so.

## The VM allows the reviewers to verify that the proofs are correct

Not really. If the authors of the paper are malicious, then they can just put a fake proof in the VM. Realistically, the reviewers aren't even going to read the makefile, so they could just put a fake script in the makefile that does `sleep 5` and prints the output without actually running the proof. However, if the reviewers are willing to spend actual effort to verify that the authors aren't malicious, how are they possibly going to do that from inside the VM? The VM is a black box prepared by the authors, so it could have a modified version of Coq or even the OS, that has a backdoor that allows the authors to prove false theorems.

If you don't trust the authors, then you can't trust the VM. You can however trust your own installation of Coq, so you might as well just download the zip file and build it yourself. If you *do* trust the authors, then *none* of this is necessary, because then you can trust they have indeed run `make` and did not lie about the output.

## What is actually happening in the artifact review process

The authors spend time setting up the VM. The reviewers then spend time installing the VM, and running `make`. What's the scientific value of this process?

There *is* some value in making sure that the code is easy to build and install from scratch, because that's what people who want to build on your artifact would have to do. So let us do that instead.