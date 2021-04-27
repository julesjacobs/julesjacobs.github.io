class Re
object Emp extends Re { override def toString() = "∅" }
object Eps extends Re { override def toString() = "ε" }
case class Chr(a:Char) extends Re { override def toString() = s"$a" }
case class Seq(a:Re, b:Re) extends Re { override def toString() = s"($a $b)" }
case class Alt(a:Re, b:Re) extends Re { override def toString() = s"($a + $b)" }
case class Star(a:Re) extends Re { override def toString() = s"$a*" }

class NFA {
  var n = 0
  var edges = Map[(Int,Int),Re]()
  def fresh() = { n += 1; n }
  def get(i:Int, j:Int) = edges.getOrElse((i,j),Emp)
  def add(i:Int, j:Int, r:Re) = edges += (i,j) -> Alt(get(i,j),r)

  def addRe(i:Int, j:Int, re:Re):Unit = {
    re match {
      case Emp =>
      case Eps => add(i,j,Eps)
      case Chr(c) => add(i,j,Chr(c))
      case Seq(a,b) =>
        val mid = fresh()
        addRe(i,mid,a)
        addRe(mid,j,b)
      case Alt(a,b) =>
        addRe(i,j,a)
        addRe(i,j,b)
      case Star(a) =>
        val mid = fresh()
        add(i,mid,Eps)
        add(mid,j,Eps)
        addRe(mid,mid,a)
    }
  }

  def elim(i:Int) = {
    // Find the self/in/out edges connected to i
    val self = get(i,i)
    val in = edges.collect{case ((a,b),r) if a != i && b == i => (a,r)}
    val out = edges.collect{case ((a,b),r) if a == i && b != i => (b,r)}

    // Delete all those edges
    edges -= (i,i)
    for((a,_) <- in) edges -= (a,i)
    for((b,_) <- out) edges -= (i,b)

    // Insert shortcut edges
    for((a,r) <- in; (b,s) <- out)
      add(a,b,Seq(r,Seq(Star(self),s)))
  }

  def toRe(initials: Set[Int], finals: Set[Int]) = {
    // Add a new start and end node and connect them to the initial and final states
    val start = fresh()
    val end = fresh()
    for(a <- initials) add(start,a,Eps)
    for(a <- finals) add(a,end,Eps)

    // Eliminate all nodes except start and end
    for(i <- 1 to start-1) elim(i)

    // Return the only edge left in the NFA
    get(start,end)
  }
}

val a = Chr('a')
val b = Chr('b')
val r1 = Seq(Star(Alt(a,b)),a)
val nfa = NFA()
val start = nfa.fresh()
val end = nfa.fresh()
nfa.addRe(start,end,r1)
nfa.edges
nfa.toRe(Set(start),Set(end))
nfa.edges