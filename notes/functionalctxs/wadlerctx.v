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

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_AddL : forall e2, ctx (λ x, Add x e2)
  | Ctx_AddR : forall n, ctx (λ x, Add (Nat n) x)
  | Ctx_If : forall e1 e2, ctx (λ x, If x e1 e2)
  | Ctx_AppL : forall e2, ctx (λ x, App x e2).

Inductive step : expr → expr → Prop :=
  | Step_add : ∀ n m, step (Add (Nat n) (Nat m)) (Nat (n+m))
  | Step_if_t : ∀ e1 e2 n, step (If (Nat (S n)) e1 e2) e1
  | Step_if_f : ∀ e1 e2, step (If (Nat 0) e1 e2) e2
  | Step_app : ∀ e1 e2 s, step (App (Lam s e1) e2) (subst s e2 e1)
  | Step_ctx : ∀ e1 e2 k, ctx k -> step e1 e2 -> step (k e1) (k e2).

Inductive ty :=
  | NatT : ty
  | FunT : ty -> ty -> ty.

Inductive typed : gmap string ty -> expr -> ty -> Prop :=
  | Var_typed : ∀ Γ x t, Γ !! x = Some t -> typed Γ (Var x) t
  | Nat_typed : ∀ Γ n, typed Γ (Nat n) NatT
  | Add_typed : ∀ Γ e1 e2,
    typed Γ e1 NatT -> typed Γ e2 NatT -> typed Γ (Add e1 e2) NatT
  | If_typed : ∀ Γ e1 e2 e3 t,
    typed Γ e1 NatT -> typed Γ e2 t -> typed Γ e3 t -> typed Γ (If e1 e2 e3) t
  | App_typed : ∀ Γ e1 e2 t t',
    typed Γ e1 (FunT t t') -> typed Γ e2 t -> typed Γ (App e1 e2) t'
  | Lam_typed : ∀ Γ x t t' e,
    typed (<[ x := t ]> Γ) e t' -> typed Γ (Lam x e) (FunT t t').

Lemma typed_mono Γ e t : typed Γ e t -> ∀ Γ', Γ ⊆ Γ' -> typed Γ' e t.
Proof.
  induction 1; econstructor; subst; eauto.
  - eapply lookup_weaken; eauto.
  - eapply IHtyped. by apply insert_mono.
Qed.

Lemma map_empty_subseteq (Γ : gmap string ty) : ∅ ⊆ Γ.
Proof.
  intros x. rewrite lookup_empty. simpl. destruct (Γ !! x); done.
Qed.

Lemma subst_typed Γ e1 e2 t t' x :
  typed ∅ e1 t -> typed (<[ x := t ]> Γ) e2 t' ->
  typed Γ (subst x e1 e2) t'.
Proof.
  remember (<[ x := t ]> Γ) as Γ'.
  intros Htyped1 Htyped2. revert Γ HeqΓ'.
  induction Htyped2; intros Γ' HeqΓ';
    simpl; try econstructor; eauto; case_decide; subst.
  - rewrite lookup_insert in H. simplify_eq.
    apply (typed_mono ∅). done. apply map_empty_subseteq.
  - constructor. by rewrite lookup_insert_ne in H.
  - constructor. by rewrite insert_insert in Htyped2.
  - constructor. eapply IHHtyped2. by rewrite insert_commute.
Qed.

Ltac inv H := inversion H; clear H; subst.

Lemma preservation e e' :
  step e e' -> ∀ t, typed ∅ e t -> typed ∅ e' t.
Proof.
  induction 1; intros t Ht;
  try solve [inv Ht; eauto using typed].
  - inv Ht. inv H2. eauto using subst_typed.
  - destruct H; inv Ht; eauto using typed.
Qed.