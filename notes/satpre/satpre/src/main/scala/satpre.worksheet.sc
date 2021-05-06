type Clause = List[Int]
type CNF = List[Clause]

val a = List(
  List(1,2),
  List(-1,3),
  List(-1,4),
  List(1,5),
  List(1,6)
)

def iabs(n : Int) = if(n < 0) -n else n

def vars(c : CNF) : Set[Int] =
  c.flatMap{cl => cl.map(iabs)}.toSet

vars(a)
