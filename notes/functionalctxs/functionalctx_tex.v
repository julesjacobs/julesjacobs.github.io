Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_AddL : forall e2, ctx (λ x, Add x e2)
  | Ctx_AddR : forall n, ctx (λ x, Add (Nat n) x)
  | Ctx_If : forall e1 e2, ctx (λ x, If x e1 e2)
  | Ctx_AppL : forall e2, ctx (λ x, App x e2).

Inductive step : expr -> expr -> Prop :=
  | Step_add : forall n m, step (Add (Nat n) (Nat m)) (Nat (n+m))
  | Step_if_t : forall e1 e2 n, step (If (Nat (S n)) e1 e2) e1
  | Step_if_f : forall e1 e2, step (If (Nat 0) e1 e2) e2
  | Step_app : forall e1 e2 s, step (App (Lam s e1) e2) (subst s e2 e1)
  | Step_ctx : forall e1 e2 k, ctx k -> step e1 e2 -> step (k e1) (k e2).