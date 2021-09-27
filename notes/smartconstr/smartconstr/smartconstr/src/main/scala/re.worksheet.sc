// Warning: code hasn't been tested

// A datatype of regular expressions, and functions to optimise them using rewrite rules

enum Re:
  case Emp
  case Eps
  case Chr(a:Char)
  case Seq(a:Re, b:Re)
  case Alt(a:Re, b:Re)
  case Star(a:Re)

// Smart constructors
// If you pass normal forms to these, they also return normal forms

def seq(a:Re, b:Re):Re =
  (a,b) match {
    case (Re.Emp,_) => Re.Emp
    case (_,Re.Emp) => Re.Emp
    case (Re.Eps,x) => x
    case (x,Re.Eps) => x
    case (Re.Seq(x,y),b) => seq(x,seq(y,b))
    case _ => Re.Seq(a,b)
  }

def alt(a:Re, b:Re):Re =
  (a,b) match {
    case (Re.Emp,x) => x
    case (x,Re.Emp) => x
    case (Re.Alt(x,y),b) => alt(x,alt(y,b))
    case _ => if(a==b) a else Re.Alt(a,b)
  }

def star(a:Re):Re =
  a match {
    case Re.Emp => Re.Eps
    case Re.Eps => Re.Eps
    case Re.Star(_) => a
    case _ => Re.Star(a)
  }

// To convert a regex to normal form, we "copy" it but call the smart constructors during copying

def nf(a:Re):Re =
  a match {
    case Re.Emp => Re.Emp
    case Re.Eps => Re.Eps
    case Re.Chr(c) => Re.Chr(c)
    case Re.Alt(a,b) => alt(nf(a),nf(b))
    case Re.Seq(a,b) => seq(nf(a),nf(b))
    case Re.Star(a) => star(nf(a))
  }

val r = Re.Alt(Re.Star(Re.Star(Re.Seq(Re.Chr('a'),Re.Star(Re.Emp)))),Re.Emp)
nf(r)

// A version of alt that also puts the alternatives in canonical order (sorted by the hashcode)
// This puts equal subexpressions next to each other, which allows us to remove duplicates

def alt1(a:Re, b:Re):Re =
  (a,b) match {
    case (Re.Emp,x) => x
    case (x,Re.Emp) => x
    case (Re.Alt(x,y),b) => alt1(x,alt1(y,b))
    case (a,Re.Alt(x,y)) =>
      if(a==x) b
      else if(a.hashCode() < x.hashCode()) Re.Alt(a,b)
      else alt1(x,alt1(a,y))
    case _ =>
      if(a==b) a
      else if(a.hashCode() < b.hashCode()) Re.Alt(a,b)
      else Re.Alt(b,a)
  }

val a = Re.Chr('a')
val b = Re.Chr('b')
alt(a,alt(b,a))
alt1(a,alt1(b,a))


// A better representation of normal forms

enum Re2:
  case Chr(a:Char)
  case Seq(rs:List[Re2])
  case Alt(rs:Set[Re2])
  case Star(r:Re2)

val emp2 = Re2.Alt(Set())
val eps2 = Re2.Seq(List())

def seq2(rs:List[Re2]):Re2 = {
  val rs2 = rs.flatMap{case Re2.Seq(rs) => rs; case x => List(x)}
  if(rs2.contains(emp2)) emp2
  else if(rs2.size == 1) rs2.head
  else Re2.Seq(rs2)
}

def alt2(rs:Set[Re2]):Re2 = {
  val rs2 = rs.flatMap{case Re2.Alt(rs) => rs; case x => Set(x)}
  if(rs2.size == 1) rs2.head
  else Re2.Alt(rs2)
}

def star2(a:Re2):Re2 =
  a match {
    case Re2.Alt(rs) if rs.isEmpty => eps2
    case Re2.Seq(rs) if rs.isEmpty => eps2
    case Re2.Star(_) => a
    case _ => Re2.Star(a)
  }

// We can define conversion functions from Re to Re2 and vice versa that put the regex in normal form
// Re.Alternatively we could always use the Re2 representation

def reToRe2(r:Re):Re2 =
  r match {
    case Re.Eps => eps2
    case Re.Emp => emp2
    case Re.Chr(c) => Re2.Chr(c)
    case Re.Alt(a,b) => alt2(Set(reToRe2(a),reToRe2(b)))
    case Re.Seq(a,b) => seq2(List(reToRe2(a),reToRe2(b)))
    case Re.Star(a) => star2(reToRe2(a))
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
    case Re2.Chr(c) => Re.Chr(c)
    case Re2.Seq(rs) => fold1(rs.map(re2ToRe), Re.Eps, Re.Seq)
    case Re2.Alt(rs) => fold1(rs.map(re2ToRe), Re.Eps, Re.Alt)
    case Re2.Star(r) => Re.Star(re2ToRe(r))
  }

val c = Re2.Chr('c')
val d = Re2.Chr('d')

val z = alt2(Set(c,d,emp2,eps2))
alt2(Set(z,z,c))
seq2(List(emp2, c, d))
re2ToRe(z)