from random import choice
ns = [(3,5),(4,4),(0,6),(5,8),(1,4)]

f = open("graph.tikz",mode="w")

for (k,(c,n)) in enumerate(ns):
  e = set([(i,(i+1)%c) for i in range(c)])
  if c == 0: c += 1
  v = set(range(c))

  for i in range(c,c+n):
    x = choice(list(v))
    v.add(i)
    e.add((i,x))

  for x in v:
    f.write("\\node (G%sV%s) [vertex] {};\n" % (k,x))

  for (x,y) in e:
    if x == y:
      f.write("\\path (G%sV%s) edge[arrow, loop above] (G%sV%s);\n" % (k,x,k,y))
    else:
      f.write("\\path (G%sV%s) edge[arrow] (G%sV%s);\n" % (k,x,k,y))
