// Warning: code hasn't been tested

// A datatype of regular expressions, and functions to optimise them using rewrite rules

val one = 1

one

class Re
object Emp extends Re { override def toString() = "∅" }
object Eps extends Re { override def toString() = "ε" }
case class Chr(a:Char) extends Re { override def toString() = s"$a" }
case class Seq(a:Re, b:Re) extends Re { override def toString() = s"($a $b)" }
case class Alt(a:Re, b:Re) extends Re { override def toString() = s"($a + $b)" }
case class Star(a:Re) extends Re { override def toString() = s"$a*" }

// Smart constructors
// If you pass normal forms to these, they also return normal forms

def seq(a:Re, b:Re):Re =
  (a,b) match {
    case (Emp,_) => Emp
    case (_,Emp) => Emp
    case (Eps,x) => x
    case (x,Eps) => x
    case (Seq(x,y),b) => seq(x,seq(y,b))
    case _ => Seq(a,b)
  }

def alt(a:Re, b:Re):Re =
  (a,b) match {
    case (Emp,x) => x
    case (x,Emp) => x
    case (Alt(x,y),b) => alt(x,alt(y,b))
    case _ => if(a==b) a else Alt(a,b)
  }

def star(a:Re):Re =
  a match {
    case Emp => Eps
    case Eps => Eps
    case Star(_) => a
    case _ => Star(a)
  }

// To convert a regex to normal form, we "copy" it but call the smart constructors during copying

def nf(a:Re):Re =
  a match {
    case Emp => Emp
    case Eps => Eps
    case Chr(c) => Chr(c)
    case Alt(a,b) => alt(nf(a),nf(b))
    case Seq(a,b) => seq(nf(a),nf(b))
    case Star(a) => star(nf(a))
  }

val r = Alt(Star(Star(Seq(Chr('a'),Star(Emp)))),Emp)
nf(r)

// A version of alt that also puts the alternatives in canonical order (sorted by the hashcode)
// This puts equal subexpressions next to each other, which allows us to remove duplicates

def alt1(a:Re, b:Re):Re =
  (a,b) match {
    case (Emp,x) => x
    case (x,Emp) => x
    case (Alt(x,y),b) => alt1(x,alt1(y,b))
    case (a,Alt(x,y)) =>
      if(a==x) b
      else if(a.hashCode() < x.hashCode()) Alt(a,b)
      else alt1(x,alt1(a,y))
    case _ =>
      if(a==b) a
      else if(a.hashCode() < b.hashCode()) Alt(a,b)
      else Alt(b,a)
  }

val a = Chr('a')
val b = Chr('b')
alt(a,alt(b,a))
alt1(a,alt1(b,a))


// A better representation of normal forms

class Re2
case class Chr2(a:Char) extends Re2
case class Seq2(rs:List[Re2]) extends Re2
case class Alt2(rs:Set[Re2]) extends Re2
case class Star2(r:Re2) extends Re2

val emp2 = Alt2(Set())
val eps2 = Seq2(List())

def seq2(rs:List[Re2]):Re2 = {
  val rs2 = rs.flatMap{case Seq2(rs) => rs
                       case x => List(x)}
  if(rs2.contains(emp2)) emp2
  else if(rs2.size == 1) rs2.head
  else Seq2(rs2)
}

def alt2(rs:Set[Re2]):Re2 = {
  val rs2 = rs.flatMap{case Alt2(rs) => rs
                       case x => Set(x)}
  if(rs2.size == 1) rs2.head
  else Alt2(rs2)
}

def star2(a:Re2):Re2 =
  a match {
    case Alt2(rs) if rs.isEmpty => eps2
    case Seq2(rs) if rs.isEmpty => eps2
    case Star2(_) => a
    case _ => Star2(a)
  }

// We can define conversion functions from Re to Re2 and vice versa that put the regex in normal form
// Alternatively we could always use the Re2 representation

def reToRe2(r:Re):Re2 =
  r match {
    case Eps => eps2
    case Emp => emp2
    case Chr(c) => Chr2(c)
    case Alt(a,b) => alt2(Set(reToRe2(a),reToRe2(b)))
    case Seq(a,b) => seq2(List(reToRe2(a),reToRe2(b)))
    case Star(a) => star2(reToRe2(a))
  }

def fold1[A](xs:Iterable[A], z:A, f:(A,A) => A):A = {
  if(xs.isEmpty) z
  else {
    var y = xs.head
    for(x <- xs.tail) y = f(x,y)
    return y
  }
}

def re2ToRe(r:Re2):Re =
  r match {
    case Chr2(c) => Chr(c)
    case Seq2(rs) => fold1(rs.map(re2ToRe), Eps, Seq)
    case Alt2(rs) => fold1(rs.map(re2ToRe), Eps, Alt)
    case Star2(r) => Star(re2ToRe(r))
  }

val x = Chr2('x')
val y = Chr2('y')

val z = alt2(Set(x,y,emp2,eps2))
alt2(Set(z,z,x))
seq2(List(emp2, x, y))
re2ToRe(z)