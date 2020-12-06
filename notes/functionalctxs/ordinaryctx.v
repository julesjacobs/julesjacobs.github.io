From stdpp Require Import decidable strings gmap.

Inductive expr :=
  | Var : string → expr
  | Nat : nat → expr
  | Add : expr → expr → expr
  | If : expr → expr → expr → expr
  | App : expr → expr → expr
  | Lam : string → expr → expr.

Fixpoint subst (x : string) (y e : expr) :=
  match e with
  | Var s => if decide (s = x) then y else e
  | Nat n => e
  | Add e1 e2 => Add (subst x y e1) (subst x y e2)
  | If e1 e2 e3 => If (subst x y e1) (subst x y e2) (subst x y e3)
  | App e1 e2 => App (subst x y e1) (subst x y e2)
  | Lam s e1 => if decide (s = x) then e else Lam s (subst x y e1)
  end.

Inductive head_step : expr → expr → Prop :=
  | Step_add : ∀ n m, head_step (Add (Nat n) (Nat m)) (Nat (n+m))
  | Step_if_t : ∀ e1 e2 n, head_step (If (Nat (S n)) e1 e2) e1
  | Step_if_f : ∀ e1 e2, head_step (If (Nat 0) e1 e2) e2
  | Step_app : ∀ e1 e2 s, head_step (App (Lam s e1) e2) (subst s e2 e1).

Inductive ctx :=
  | Ctx_Hole : ctx
  | Ctx_AddL : expr → ctx → ctx
  | Ctx_AddR : nat → ctx → ctx
  | Ctx_If : expr → expr → ctx → ctx
  | Ctx_AppL : expr → ctx → ctx.

Fixpoint fill E x :=
  match E with
  | Ctx_Hole => x
  | Ctx_AddL e2 E' => Add (fill E' x) e2
  | Ctx_AddR n E' => Add (Nat n) (fill E' x)
  | Ctx_If e1 e2 E' => If (fill E' x) e1 e2
  | Ctx_AppL e2 E' => App (fill E' x) e2
  end.

Inductive step : expr → expr → Prop :=
  | Step_ctx : ∀ E e1 e2, head_step e1 e2 → step (fill E e1) (fill E e2).