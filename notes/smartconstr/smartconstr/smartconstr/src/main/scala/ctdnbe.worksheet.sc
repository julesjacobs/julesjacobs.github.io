// Warning: code hasn't been tested

// Conventional ype directed normalization by evaluation for simply typed lambda calculus with pairs

// Types

class Ty
case class Base(name:String) extends Ty
case class Arrow(a:Ty, b:Ty) extends Ty

// HOAS lambda terms

class Sem
case class LamS(f:Sem => Sem) extends Sem
case class AppS(a:Sem, b:Sem) extends Sem

// Smart constructor for AppS

def appS(a:Sem, b:Sem):Sem =
  a match {
    case LamS(f) => f(b)
    case _ => AppS(a,b)
  }

// Normalizing a Sem term is easy

def gen(t:Ty, e:Sem):Sem = e

def norm(t:Ty, e:Sem):Sem =
  (t,e) match {
    case (Arrow(a,b),LamS(f)) => LamS(x => norm(b,f(gen(a,x))))
  }



class Tm
case class Var(x:String) extends Tm
case class Lam(x:String, a:Tm) extends Tm
case class App(a:Tm, b:Tm) extends Tm
case class Pair(a:Tm, b:Tm) extends Tm
case class Fst(a:Tm) extends Tm
case class Snd(a:Tm) extends Tm

case class TmS(a:Tm) extends Sem




// Conversion from Tm to Sem

def eval(env:Map[String,Sem], a:Tm):Sem =
  a match {
    case Var(x) => env(x)
    case Lam(x, a) => LamS(v => eval(env + (x -> v), a))
    case App(a,b) => AppS(eval(env,a),eval(env,b))
  }

def tmToSem(a:Tm):Sem = eval(Map(),a)

// Conversion from Sem to Tm

var n = 0
def fresh() = { n += 1; s"x$n" }

def reify(a:Sem):Tm =
  a match {
    case TmS(a) => a
    case LamS(f) => val x = fresh(); Lam(x, reify(f(TmS(Var(x)))))
    case AppS(a,b) => App(reify(a),reify(b))
  }

def semToTm(a:Sem):Tm = reify(a)

// Example

val z = LamS(f => LamS(x => x))
val s = LamS(n => LamS(f => LamS(z => AppS(AppS(n,f),AppS(f,z)))))

val one = AppS(s,z)
val two = AppS(s,one)

reify(two)
reify(norm(two))