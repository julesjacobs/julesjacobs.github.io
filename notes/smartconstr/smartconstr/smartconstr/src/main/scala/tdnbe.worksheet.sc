// Type directed normalization by evaluation for simply typed lambda calculus

// Lambda terms with named variables
enum Tm:
  case Var(x:String)
  case Lam(x:String, a:Tm)
  case App(a:Tm, b:Tm)

// HOAS lambda terms
enum Hs:
  case Lam(f:Hs => Hs)
  case App(a:Hs, b:Hs)
  case Res(a:Object) // hack for fold

def fold[T](a:Hs, app : (T,T) => T, lam : (T => T) => T) : T =
  a match {
    case Hs.Res(x) => x.asInstanceOf[T]
    case Hs.Lam(f) => lam(t => fold(f(Hs.Res(t.asInstanceOf[Object])), app, lam))
    case Hs.App(a,b) => app(fold(a, app, lam), fold(b, app, lam))
  }


// Conversion from Tm to Hs

def eval(env:Map[String,Hs], a:Tm):Hs =
  a match {
    case Tm.Var(x) => env(x)
    case Tm.Lam(x, a) => Hs.Lam(v => eval(env + (x -> v), a))
    case Tm.App(a,b) => Hs.App(eval(env,a),eval(env,b))
  }

def toHs(a:Tm):Hs = eval(Map(),a)


// Conversion from Hs to T

var n = 0
def fresh() = { n += 1; s"x$n" }

def freshLam(f : Tm => Tm):Tm = { val x = fresh(); Tm.Lam(x, f(Tm.Var(x))) }

def toT(a:Hs):Tm = fold[Tm](a, Tm.App, freshLam)


// Types
enum Ty:
  case Base(name:String)
  case Arrow(a:Ty, b:Ty)

// Semantic domain
enum Sem:
  case Syn(a:Hs) // Sem_Base = Sem.Syntactic terms Hs
  case Lam(f:Sem => Sem) // Sem_{A -> B} = Sem_A -> Sem_B

// reflect η expands
// reflect : Hs_t -> Sem_t
def reflect(t:Ty, x:Hs):Sem =
  t match {
    case Ty.Arrow(a,b) => Sem.Lam(y => reflect(b, Hs.App(x, reify(a,y))))
    case Ty.Base(_) => Sem.Syn(x)
  }

// reify : Sem_t -> Hs_t
def reify(t:Ty, x:Sem):Hs =
  (t,x) match {
    case (Ty.Arrow(a,b),Sem.Lam(f)) => Hs.Lam(y => reify(b, f(reflect(a, y))))
    case (Ty.Base(_), Sem.Syn(y)) => y
  }


// Smart constructor
// appS : Sem_{A -> B} -> Sem_A -> Sem_B
def appS(a:Sem, b:Sem):Sem =
  a match {
    case Sem.Lam(f) => f(b)
    // Types guarantee that we don't need any other case!
  }

// meaning : Hs_t -> Sem_t
def meaning(x:Hs):Sem = fold[Sem](x, appS, Sem.Lam)

// HOAS -> HOAS NbE
// nbe : Hs_t -> Hs_t
def nbe(t:Ty, e:Hs) = reify(t, meaning(e))

// nbeT : Tm_t -> Tm_t
def nbeT(t:Ty, e:Tm) = toT(nbe(t,toHs(e)))


// SKK example from wikipedia

val k = Hs.Lam(x => Hs.Lam(y => x))
val s = Hs.Lam(x => Hs.Lam(y => Hs.Lam(z => Hs.App(Hs.App(x,z), Hs.App(y,z)))))
val skk = Hs.App(Hs.App(s,k),k)

toT(skk)

val ta = Ty.Arrow(Ty.Base("a"),Ty.Base("a"))

toT(nbe(ta, skk))

val taa = Ty.Arrow(ta, ta)

toT(nbe(taa, skk))