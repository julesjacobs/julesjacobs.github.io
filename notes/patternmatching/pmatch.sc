// A pattern matching compiler

type ID = String

// We abstract the body of each clause as a call E(x1,...,xk)
// In a full compiler, this would be an arbitrary piece of code
case class Call(name:String, args:List[ID])

// A pattern is either a variable or a constructor
// We could extend this, e.g. with guards
class Pat
case class Var(name:ID) extends Pat
case class Constr(name:String, args:List[Pat]) extends Pat

// Our pattern matching construct is a list of clauses
// A clause consists of bound variables that will be matched against patterns
// This is different than an ordinary match like in ML, where we match multiple patterns against one value
// Our match conceptually looks like this:
//   match
//   | x = Plus(Mul(a,b),c), y = Mul(d,e)    =>  body1
//   | x = Plus(c,Mul(a,b)), z = Plus(d,e)   =>  body1
//   | ...
// Where x,y,z are bound variables that we match against patterns.
// An ML-like match such as:
//   match x with
//   | Mul(Add(a,b),Add(c,d)) => body1
//   | Mul(c,Add(a,b)) => body2
//   | else => body3
// Can be translated to:
//   match
//   | x = Mul(Add(a,b),Add(c,d)) => body1
//   | x = Mul(c,Add(a,b)) => body2
//   | else => body3
// This format makes it significantly simpler to compile, because during the compilation process, a match
// on a single variable turns into a match on multiple variables. For example, if we branch on x, we get:
//   match
//   | x = Mul(y,z) =>
//        match
//        | y = Add(a,b), z = Add(c,d) => body1
//        | c = y, z = Add(a,b) => body2
//   | else => body3
// As you can see, compilation of a match where each clause pattern matches against only a single variable,
// turns into a nested match where we may match against multiple variables.
// The alternative would be to match against a tuple, but using multiple variables is better, because
// it gives us more flexibility: we can simplify equations like c = y, which means that it's no longer
// the case that all clauses match agaist the same set of variables. That is, we turn the inner match above into:
//        match
//        | y = Add(a,b), z = Add(c,d) => body1
//        | z = Add(a,b) => body2[c := y]
// Tuples on the other hand tend to accumulate a lot of unnecessary matches against variables, and also require
// an extra step in the final codegen.
case class Clause(pats: Map[ID, Pat], body: Call)
type Match = List[Clause]

// We compile pattern matching to case trees
// A node in a case tree is either a Test, which pattern matches a variable against a single constructor
// Or it is the final node Run, which runs some code (coming from the body of a clause)
abstract class CaseTree {
  def pp() : Unit
}
case class Test(x:ID, constr:String, elems:List[ID], yes:CaseTree, no:CaseTree) extends CaseTree {
  def pp() = {
    val args = elems.mkString(",")
    print(s"if $constr($args) = $x:")
    indent { () => ln(); yes.pp() }
    ln()
    print(s"else: ")
    no.pp()
  }
}
case class Run(code: Call) extends CaseTree {
  def pp() = {
    val args = code.args.mkString(",")
    print(s"${code.name}($args)")
  }
}

var indentLevel = 0
def indent(f : () => Unit) = {
  indentLevel += 1
  f()
  indentLevel -= 1
}
def ln() = {
  print("\n" + ("  " * indentLevel))
}

var k = 0
def fresh() : String = {
  k += 1
  return s"x$k"
}

// This is the main function that builds a case tree for a pattern matching problem
def genMatch(clauses : Seq[Clause]) : CaseTree = {
  if(clauses.isEmpty) assert(false, "Non-exhaustive pattern")
  val clauses2 = clauses.map(substVarEqs)
  val Clause(pats,bod) = clauses2.head  // We always try to determine if the first clause matches first, to avoid doing unnecessary work
  if(pats.isEmpty) return Run(bod)
  val branchVar = branchingHeuristic(pats, clauses2)
  // Now we branch on branchVar by testing against the constructors in pats
  // We generate the new clauses in the yes and no branch:
  //   The yes branch will contain all clauses that have the same constructor for that var + clauses that don't match on that var at all
  //   The no branch will contain all clauses that have a different constructor for that var + clause that don't match on that var at all
  val Constr(constrname, args) = pats(branchVar) // We know that the pattern must be a constructor at this point, because all vars have been subtituted
  var yes = collection.mutable.Buffer[Clause]()
  var no = collection.mutable.Buffer[Clause]()
  val vars = args.map(x => fresh())
  for(Clause(pats,bod) <- clauses2){
    pats.get(branchVar) match {
      case Some(Constr(constrname2, args2)) =>
        if(constrname == constrname2){
          assert(args.length == args2.length, s"Constructors with inconsistent sizes: $constrname")
          yes += Clause(pats - branchVar ++ vars.zip(args2), bod)
        }else{
          no += Clause(pats,bod)
        }
      case None =>
        // Clauses that don't match on that var are duplicated. So we want to choose our branching heuristic to minimize this
        yes += Clause(pats,bod)
        no += Clause(pats,bod)
    }
  }
  return Test(branchVar, constrname, vars, genMatch(yes.toSeq), genMatch(no.toSeq))
}

// This takes a clause with plain variable matches such as (c = x) and substitutes them
def substVarEqs(clause: Clause): Clause = {
  val Clause(pats, Call(name, args)) = clause
  val substitution = pats.collect{ case (v,Var(w)) => w -> v }
  val patterns = pats.filter((v,p) => p.isInstanceOf[Constr])
  return Clause(patterns.toMap, Call(name, args.map(v => substitution.getOrElse(v, v))))
}

// Heuristically select a variable to branch on
// We want to do that in such a way as to generate a the best final case tree
// It's not entirely clear what is best: smallest total size, or maybe a bigger case tree can sometimes be more efficient to execute
// Due to the hash consing it is hard to predict which case tree will actually be smallest
// One solution might be to try all possible branchings, and choose the best case tree using some cost metric
// Note sure if that's worth it, since the case trees are already quite good with a simple heuristic: the one that locally causes the least duplication
var heuristic = "good"
def branchingHeuristic(pats: Map[String, Pat], clauses: Seq[Clause]): String =
  if(heuristic == "good") pats.keys.maxBy(v => clauses.count{case Clause(ps,bod) => ps.contains(v)})
  else if(heuristic == "bad") pats.keys.minBy(v => clauses.count{case Clause(ps,bod) => ps.contains(v)})
  else if(heuristic == "none") pats.keys.head
  else assert(false, s"Bad heuristic: $heuristic")


// Example pattern match
val x = Var("x")
val y = Var("y")
val z = Var("z")
val zero = Constr("Zero", List())
def suc(a: Pat) = Constr("Suc", List(a))
def add(a: Pat, b: Pat) = Constr("Add", List(a, b))
def mul(a: Pat, b: Pat) = Constr("Mul", List(a, b))
def pow(a: Pat, b: Pat) = Constr("Pow", List(a, b))

val clauses = List(
  add(zero, x) -> Call("A", List("x")),
  add(x,zero) -> Call("B", List("x")),
  mul(zero,x) -> Call("C", List("x")),
  mul(x,zero) -> Call("D", List("x")),
  add(suc(x), y) -> Call("E", List("x","y")),
  add(x, suc(y)) -> Call("F", List("x","y")),
  mul(suc(x), y) -> Call("G", List("x","y")),
  mul(x, suc(y)) -> Call("H", List("x","y")),
  mul(add(x, y), z) -> Call("I", List("x","y","z")),
  mul(z, add(x, y)) -> Call("J", List("x","y","z")),
  mul(mul(x, y), z) -> Call("K", List("x","y","z")),
  pow(x, suc(y)) -> Call("L", List("x","y")),
  pow(x, zero) -> Call("M", List("x")),
  suc(add(zero,zero)) -> Call("Q1",List()),
  suc(add(x,y)) -> Call("Q2", List("x","y")),
  x -> Call("N", List("x"))
)

val exampleMatch : Match = clauses.map((pat,bod) => Clause(Map("it" -> pat), bod)).toList

val result = genMatch(exampleMatch)
result.pp()

// Output:
//   (heuristics make no difference for this example)
//
// test(Add(x1,x2) = it):
//   test(Zero() = x1):
//     test(Zero() = x2):
//       Z()
//     A(x2)
//   test(Zero() = x2):
//     B(x1)
//   test(Suc(x3) = x1):
//     E(x3,x2)
//   test(Suc(x4) = x2):
//     F(x1,x4)
//   N(it)
// test(Mul(x5,x6) = it):
//   test(Zero() = x5):
//     C(x6)
//   test(Zero() = x6):
//     D(x5)
//   test(Suc(x7) = x5):
//     G(x7,x6)
//   test(Suc(x8) = x6):
//     H(x5,x8)
//   test(Add(x9,x10) = x5):
//     I(x9,x10,x6)
//   test(Add(x11,x12) = x6):
//     J(x11,x12,x5)
//   test(Mul(x13,x14) = x5):
//     K(x13,x14,x6)
//   N(it)
// test(Pow(x15,x16) = it):
//   test(Suc(x17) = x16):
//     L(x15,x17)
//   test(Zero() = x16):
//     M(x15)
//   N(it)
// test(Suc(x18) = it):
//   test(Add(x19,x20) = x18):
//     test(Zero() = x19):
//       test(Zero() = x20):
//         Q1()
//       Q2(x19,x20)
//     Q2(x19,x20)
//   N(it)
// N(it)


// Example from: Compiling Pattern Matching to Good Decision Trees, Luc Maranget
// -----------------------------------------------------------------------------
//
// let rec run a s e c = match a,s,c with
// | _,_,Ldi i::c -> 1
// | _,_,Push::c -> 2
// | Int n2,Val (Int n1)::s,IOp op::c -> 3
// | Int 0,_,Test (c2,_)::c -> 4
// | Int _,_,Test (_,c3)::c -> 5
// | _,_,Extend::c -> 6
// | _,_,Search k::c -> 7
// | _,_,Pushenv::c -> 8
// | _,Env e::s,Popenv::c -> 9
// | _,_,Mkclos cc::c -> 10
// | _,_,Mkclosrec cc::c -> 11
// | Clo (cc,ce),Val v::s,Apply::c -> 12
// | a,(Call c::Env e::s),[] -> 13
// | a,[],[] -> 14

val nil = Constr("nil",List())
def cons(a:Pat,b:Pat) = Constr("cons", List(a,b))
def int(a:Pat) = Constr("int", List(a))
def vall(a:Pat) = Constr("val", List(a))
def test(a:Pat,b:Pat) = Constr("test", List(a,b))
val i = Var("i")
val c = Var("c")
val e = Var("e")
val a = Var("a")
val cc = Var("cc")
val op = Var("op")


k=0
val clauses2 = List(
  Map("c" -> Constr("Ldi",List(cons(i,c)))),
  Map("c" -> Constr("Push",List(c))),
  Map("a" -> int(Var("n2")), "s" -> vall(int(Var("n1"))), "c" -> Constr("iop",List(op,c))),
  Map()
).map(x => Clause(x,Call(fresh(),List())))

val result2 = genMatch(clauses2)
result2.pp()


val clauses3 = List(
  add(add(x,x),zero) -> Call("A",List()),
  add(mul(x,x),zero) -> Call("B",List()),
  add(x,pow(x,x)) -> Call("C",List()),
  add(x,mul(x,x)) -> Call("F",List()),
  add(x,zero) -> Call("G",List()),
  x -> Call("Z", List("x"))
)

val exampleMatch3 : Match = clauses3.map((pat,bod) => Clause(Map("it" -> pat), bod)).toList

heuristic = "good"
val result3 = genMatch(exampleMatch3)
result3.pp()

// test(Add(x14,x15) = it):
//   test(Zero() = x15):
//     test(Add(x16,x17) = x14):
//       A()
//     test(Mul(x18,x19) = x14):
//       B()
//     G()
//   test(Pow(x20,x21) = x15):
//     C()
//   test(Mul(x22,x23) = x15):
//     F()
//   Z(it)
// Z(it)

heuristic = "bad"
val result4 = genMatch(exampleMatch3)
result4.pp()

// test(Add(x24,x25) = it):
//   test(Add(x26,x27) = x24):
//     test(Zero() = x25):
//       A()
//     test(Pow(x28,x29) = x25):
//       C()
//     test(Mul(x30,x31) = x25):
//       F()
//     Z(it)
//   test(Mul(x32,x33) = x24):
//     test(Zero() = x25):
//       B()
//     test(Pow(x34,x35) = x25):
//       C()
//     test(Mul(x36,x37) = x25):
//       F()
//     Z(it)
//   test(Pow(x38,x39) = x25):
//     C()
//   test(Mul(x40,x41) = x25):
//     F()
//   test(Zero() = x25):
//     G()
//   Z(it)
// Z(it)




// Thoughts:
// - Most real pattern matches are relatively simple; they don't have any tricky cases that lead to duplication
// - Pretty much any reasonable algorithm will do well on those
// - Thus which pattern matching algorithm you use probably doesn't matter much
// - Sharing can be done as a post pass that generically shares CFG nodes
//      This is fine, because there seems to be little danger of code explosion, so trying to generate shared trees seems to be a waste of effort
// - Sharing further makes the choice of algorithm less relevant:
//      In the example above, sharing compresses the case tree from the bad heuristic to be pretty much equivalent to the good heuristic
//      It's actually difficult to come up with an example where the simple "good" heuristic produces suboptimal code when you have a sharing post-pass
// - It might be important to not be forced to check all constructors of a data type in an n-way branch
// - But maybe n-way branches should be done if possible, because they might have more efficient codegen (e.g. jump table)
// - We do want to use the types to eliminate dead cases, and to eagerly test/assert cases when only one constructor is still possible
// - It might actually be feasible to enumerate all possible pattern matching trees, if we always branch on a var with a constructor in the first clause, because those aren't that many choices
// - Luc Maranget shows that pattern matching compilation matters very little in practice, only 2% size difference, and in his best example 5% speed difference for compiled code on amd64.

// Compile to single var non-nested match expressions, but multi-way + default branches. If no default branch, then the last branch is forced (given by types).
// Prefer testing the same variable multiple times to help good codegen.