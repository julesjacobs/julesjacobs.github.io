(* From iris Require Import bi. *)

(* Simplifies equations by doing substitution and injection. *)
Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | _ => congruence || (progress subst)
  end.

Ltac inv H := inversion H; clear H; simplify_eq.


Inductive even : nat -> Prop :=
  | O_even : even 0
  | SS_even n : even n -> even (S (S n)).

Inductive bha : nat -> Prop :=
  | O_bha : bha 0.

Inductive bho : nat -> Prop := .

Lemma foo_even : even 10.
Proof.
  eauto 10 using even.
Qed.


Ltac rew := repeat
  match goal with
  | _ => progress simpl in *
  | _ => progress simplify_eq
  | H : _ |- _ => rewrite H in * by solve [auto]
  end.

Ltac simp := repeat
  match goal with
  | H : False |- _ => destruct H
  | H : ex _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : _ * _ |- _ => destruct H
  | H : ?P -> ?Q, H2 : ?P |- _ => specialize (H H2)
  | |- forall x,_ => intro
  | _ => progress simpl in *
  | _ => progress simplify_eq
  | _ => solve [eauto]
  | _ => solve [econstructor; eauto]
  end.

Ltac destr :=
  match goal with
  | H : _ \/ _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- context[if ?x then _ else _] => destruct x eqn:?
  | |- context[match ?x with _ => _ end] => destruct x eqn:?
  | H : context[if ?x then _ else _] |- _ => destruct x eqn:?
  | H : context[match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Lemma foo (n: nat) (b: bool) :
  (if b then n else n) = n -> n = n+1.
Proof.
  intro.
  destr; simp.

Tactic Notation "butone" tactic(tac) := (tac; fail) || (tac; [idtac]).

Ltac simpd := simp; do 5 try butone (destr; simp).

From iris Require Import bi.

Lemma test (P Q R : Prop) : (P ∧ Q) ∨ Q -> (Q -> False) -> P ∧ Q.
Proof.
  simpd.
Qed.

Lemma test' (n:nat) (b:bool) : (if decide (n=0) then 0 else n) = n.
Proof.
  simpd.
Qed.

Lemma add_0 n : add n 0 = n.
Proof.
  induction n; simp.
Qed.

Lemma add_S n m : add n (S m) = S (add n m).
Proof.
  induction n; simp.
Qed.