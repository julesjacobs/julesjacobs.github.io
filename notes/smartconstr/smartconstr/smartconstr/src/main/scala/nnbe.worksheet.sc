// Warning: code hasn't been tested

// Normalization by evaluation for untyped lambda calculus


// Lambda terms with named variables

class Tm
case class Var(x:String) extends Tm
case class Lam(x:String, a:Tm) extends Tm
case class App(a:Tm, b:Tm) extends Tm

// HOAS lambda terms

class HTm
case class LamH(f:HTm => HTm) extends HTm
case class AppH(a:HTm, b:HTm) extends HTm
case class ResH(a:Object) extends HTm // hack for elim

def elim[T](a:HTm, app : (T,T) => T, lam : (T => T) => T) : T =
  a match {
    case ResH(x) => x.asInstanceOf[T]
    case LamH(f) => lam(t => elim(f(ResH(t.asInstanceOf[Object])), app, lam))
    case AppH(a,b) => app(elim(a, app, lam), elim(b, app, lam))
  }

def app(a:HTm, b:HTm):HTm =
  a match {
    case LamH(f) => f(b)
    case _ => AppH(a,b)
  }

def norm(a:HTm):HTm = elim[HTm](a, app, LamH)


// Normal and neutral forms

class Normal
case class LamNo(f:Normal => Normal) extends Normal

class Neutral extends Normal
case class AppNe(a:Neutral, b:Normal) extends Neutral


// Smart constructor for AppH

def appNo(a:Normal, b:Normal):Normal =
  a match {
    case LamNo(f) => f(b)
    case a:Neutral => AppNe(a,b)
  }

// Normalizing a HTm term to Normal

def toNorm(a:HTm):Normal = elim[Normal](a, appNo, LamNo)



// Conversion from Tm to HTm

def eval(env:Map[String,HTm], a:Tm):HTm =
  a match {
    case Var(x) => env(x)
    case Lam(x, a) => LamH(v => eval(env + (x -> v), a))
    case App(a,b) => AppH(eval(env,a),eval(env,b))
  }

def toHTm(a:Tm):HTm = eval(Map(),a)



// Conversion from HTm to Tm

var n = 0
def fresh() = { n += 1; s"x$n" }

def lamFresh(f : Tm => Tm):Tm = { val x = fresh(); Lam(x, f(Var(x))) }

def toTm(a:HTm):Tm = elim[Tm](a, App, lamFresh)

// Example

val z = LamH(f => LamH(x => x))
val s = LamH(n => LamH(f => LamH(z => AppH(AppH(n,f),AppH(f,z)))))

val one = AppH(s,z)
val two = AppH(s,one)

toTm(two)
toTm(norm(two))