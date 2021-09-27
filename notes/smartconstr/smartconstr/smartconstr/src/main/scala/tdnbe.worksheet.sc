// Warning: code hasn't been tested

// Type directed normalization by evaluation for simply typed lambda calculus with pairs

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



// Types

class Ty
case class Base(name:String) extends Ty
case class Arrow(a:Ty, b:Ty) extends Ty

// Semantic domain

class Sem
case class Syn(a:HTm) extends Sem // syntactic values
case class LamS(f:Sem => Sem) extends Sem


// Creates η expanded term
def reflect(t:Ty, x:HTm):Sem =
  t match {
    case Arrow(a,b) => LamS(y => reflect(b, AppH(x, reify(a,y))))
    case Base(_) => Syn(x)
  }

// Convert Sem -> HTm
def reify(t:Ty, x:Sem):HTm =
  (t,x) match {
    case (Arrow(a,b),LamS(f)) => LamH(y => reify(b, f(reflect(a, y))))
    case (Base(_), Syn(y)) => y
  }


// Smart constructor

def appS(a:Sem, b:Sem):Sem =
  a match {
    case LamS(f) => f(b)
    // Types guarantee that we don't need any other case!
  }

// Convert HTm -> Sem
def meaning(x:HTm):Sem = elim[Sem](x, appS, LamS)

def nbe(t:Ty, e:HTm) = reify(t, meaning(e))

val k = LamH(x => LamH(y => x))
val s = LamH(x => LamH(y => LamH(z => AppH(AppH(x,z), AppH(y,z)))))
val skk = AppH(AppH(s,k),k)

toTm(skk)

val tab = Arrow(Base("a"),Base("b"))

toTm(nbe(tab, skk))

val tabab = Arrow(tab, tab)

toTm(nbe(tabab, skk))