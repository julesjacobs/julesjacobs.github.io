// Warning: code hasn't been tested

// Normalization by hereditary substitution for De Bruijn terms

class Tm
case class Var(n:Int) extends Tm
case class Lam(a:Tm) extends Tm
case class App(a:Tm,b:Tm) extends Tm

// Renaming

def liftR(f : Int => Int): Int => Int =
  (n) => if(n==0) 0 else f(n-1) + 1

def rename(a:Tm, f:Int => Int):Tm =
  a match {
    case Var(n) => Var(f(n))
    case Lam(a) => Lam(rename(a,liftR(f)))
    case App(a,b) => App(rename(a,f),rename(b,f))
  }

// Substitution

def shift(e:Tm, f:Int => Tm):Int => Tm =
  (n) => if(n==0) e else f(n-1)

def liftS(f : Int => Tm):Int => Tm =
  shift(Var(0), k => rename(f(k), (_+1)))

def subst(a:Tm, f:Int => Tm):Tm =
  a match {
    case Var(n) => f(n)
    case Lam(a) => Lam(subst(a,liftS(f)))
    case App(a,b) => App(subst(a,f),subst(b,f))
  }

def subst1(a:Tm, b:Tm):Tm = subst(a, shift(b,Var))

// Hereditary substitution

def app(a:Tm, b:Tm):Tm =
  a match {
    case Lam(e) => subst1(e, b)
    case _ => App(a,b)
  }

def hsubst(a:Tm, f:Int => Tm):Tm =
  a match {
    case Var(n) => f(n)
    case Lam(a) => Lam(hsubst(a,liftS(f)))
    case App(a,b) => app(hsubst(a,f),hsubst(b,f))
  }

def hsubst1(a:Tm, b:Tm):Tm = hsubst(a, shift(b,Var))

def norm(a:Tm):Tm =
  a match {
    case Var(n) => Var(n)
    case Lam(a) => Lam(norm(a))
    case App(a,b) => app(norm(a),norm(b))
  }