From stdpp Require Import decidable strings gmap.

Inductive expr :=
  | Var : string -> expr
  | Nat : nat -> expr
  | Add : expr -> expr -> expr
  | If : expr -> expr -> expr -> expr
  | App : expr -> expr -> expr
  | Lam : string -> expr -> expr.

Fixpoint subst (x : string) (y e : expr) :=
  match e with
  | Var s => if decide (s = x) then y else e
  | Nat n => e
  | Add e1 e2 => Add (subst x y e1) (subst x y e2)
  | If e1 e2 e3 => If (subst x y e1) (subst x y e2) (subst x y e3)
  | App e1 e2 => App (subst x y e1) (subst x y e2)
  | Lam s e1 => if decide (s = x) then e else Lam s (subst x y e1)
  end.

Inductive head_step : expr -> expr -> Prop :=
  | Step_add : ∀ n m, head_step (Add (Nat n) (Nat m)) (Nat (n+m))
  | Step_if_t : ∀ e1 e2 n, head_step (If (Nat (S n)) e1 e2) e1
  | Step_if_f : ∀ e1 e2, head_step (If (Nat 0) e1 e2) e2
  | Step_app : ∀ e1 e2 s, head_step (App (Lam s e1) e2) (subst s e2 e1).

Inductive ctx1 : (expr -> expr) -> Prop :=
  | Ctx_AddL : ∀ e2, ctx1 (λ x, Add x e2)
  | Ctx_AddR : ∀ n, ctx1 (λ x, Add (Nat n) x)
  | Ctx_If : ∀ e1 e2, ctx1 (λ x, If x e1 e2)
  | Ctx_AppL : ∀ e2, ctx1 (λ x, App x e2).

Inductive ctx : (expr -> expr) -> Prop :=
  | Ctx_nil : ctx (λ x, x)
  | Ctx_cons : ∀ k1 k2, ctx1 k1 -> ctx k2 -> ctx (k1 ∘ k2).

Inductive step : expr -> expr -> Prop :=
  | Step_step : ∀ k e1 e2, ctx k -> head_step e1 e2 -> step (k e1) (k e2).

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

Lemma preservation e e' t :
  step e e' -> typed ∅ e t -> typed ∅ e' t.
Proof.
  intros Hstep. revert t.
  destruct Hstep as [e1 e2 k Hctx Hstep].
  induction Hctx as [|k1 k2 Hctx1 Hctx IHHctx]; intros t Htyped.
  - destruct Hstep; inv Htyped; try econstructor; eauto.
    inv H2. rewrite-> insert_empty in H1.
    eapply subst_typed; eauto.
  - destruct Hctx1; inv Htyped; econstructor; eauto.
Qed.

Inductive value : expr -> Prop :=
  | Val_nat : ∀ n, value (Nat n)
  | Val_lam : ∀ x e, value (Lam x e).

Lemma ctx_step k e1 e2 :
  ctx1 k -> step e1 e2 -> step (k e1) (k e2).
Proof.
  intros ?[]. eapply (Step_step (λ x, (k (k0 x)))); by try constructor.
Qed.

Ltac do_head_step := eexists; eapply (Step_step (λ x, x)); by constructor.
Ltac do_ctx_step k := eexists; eapply (ctx_step k); by constructor.

Lemma progress e t :
  typed ∅ e t -> value e ∨ ∃ e', step e e'.
Proof.
  remember ∅ as Γ.
  induction 1; subst.
  - rewrite lookup_empty in H. simplify_eq.
  - left. constructor.
  - right. destruct IHtyped1 as [|[]]; eauto.
    + inv H1;[|inv H].
      destruct IHtyped2 as [|[]]; eauto.
      * inv H1; [|inv H0]. do_head_step.
      * destruct H1. do_ctx_step (λ x, (Add (Nat n) x)).
    + destruct H1. do_ctx_step (λ x, Add x e2).
  - right. destruct IHtyped1 as [|[]]; eauto.
    + inv H2;[|inv H]. destruct n; do_head_step.
    + destruct H2. do_ctx_step (λ x, If x e2 e3).
  - right. destruct IHtyped1 as [|[]]; eauto.
    + inv H1;[inv H|]. do_head_step.
    + destruct H1. do_ctx_step (λ x, App x e2).
  - left. constructor.
Qed.