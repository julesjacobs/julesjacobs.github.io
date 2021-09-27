// Warning: code hasn't been tested

// Normalization by hereditary substitution for De Bruijn terms

enum Db:
  case Var(x:Int)
  case Lam(a:Db)
  case App(a:Db, b:Db)

// Renaming

def liftR(f : Int => Int): Int => Int =
  (n) => if(n==0) 0 else f(n-1) + 1

def rename(a:Db, f:Int => Int):Db =
  a match {
    case Db.Var(n) => Db.Var(f(n))
    case Db.Lam(a) => Db.Lam(rename(a,liftR(f)))
    case Db.App(a,b) => Db.App(rename(a,f),rename(b,f))
  }

// Substitution

def shift(e:Db, f:Int => Db):Int => Db =
  (n) => if(n==0) e else f(n-1)

def liftS(f : Int => Db):Int => Db =
  shift(Db.Var(0), k => rename(f(k), (_+1)))

def subst(a:Db, f:Int => Db):Db =
  a match {
    case Db.Var(n) => f(n)
    case Db.Lam(a) => Db.Lam(subst(a,liftS(f)))
    case Db.App(a,b) => Db.App(subst(a,f),subst(b,f))
  }

def subst1(a:Db, b:Db):Db = subst(a, shift(b,Db.Var))

// Hereditary substitution

def app(a:Db, b:Db):Db =
  a match {
    case Db.Lam(e) => subst1(e, b)
    case _ => Db.App(a,b)
  }

def hsubst(a:Db, f:Int => Db):Db =
  a match {
    case Db.Var(n) => f(n)
    case Db.Lam(a) => Db.Lam(hsubst(a,liftS(f)))
    case Db.App(a,b) => app(hsubst(a,f),hsubst(b,f))
  }

def hsubst1(a:Db, b:Db):Db = hsubst(a, shift(b,Db.Var))

def norm(a:Db):Db =
  a match {
    case Db.Var(n) => Db.Var(n)
    case Db.Lam(a) => Db.Lam(norm(a))
    case Db.App(a,b) => app(norm(a),norm(b))
  }