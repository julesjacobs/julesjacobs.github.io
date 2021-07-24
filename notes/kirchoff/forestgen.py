from random import choice
ns = [5,10,14,4,7]

f = open("forest.tikz",mode="w")

for (k,n) in enumerate(ns):
  v = set([0])
  e = set()

  for i in range(1,n):
    x = choice(list(v))
    v.add(i)
    e.add((i,x))

  for x in v:
    f.write("\\node (G%sV%s) [vertex] {};\n" % (k,x))

  for (x,y) in e:
    f.write("\\path (G%sV%s) edge[arrow] (G%sV%s);\n" % (k,x,k,y))
