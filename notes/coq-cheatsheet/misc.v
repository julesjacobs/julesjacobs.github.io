(* From iris Require Import bi. *)

(* Simplifies equations by doing substitution and injection. *)
Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : ?f _ = ?f _ |- _ => progress injection H as H
  | H : ?f _ _ = ?f _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as H
  | H : ?x = ?x |- _ => clear H
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

Lemma test n : bho n -> bha n -> even n -> False.
Proof.
  intros H1 H2 H3.
  inversion H1; (fail || idtac); [|fail..].
  inversion H; [idtac].
  inv H.


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
  | _ => solve eauto
  | H : _ \/ _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- context[if ?x then _ else _] => destruct ?x eqn:?
  | |- context[match ?x with _ => _ end] => destruct ?x eqn:?
  | H : context[if ?x then _ else _] |- _ => destruct ?x eqn:?
  | H : context[match ?x with _ => _ end] |- _ => destruct ?x eqn:?
  end.

Inductive even : nat -> Prop :=
  | O_even : even 0
  | SS_even n : even n -> even (S (S n)).

Fixpoint add (n m : nat) :=
  match n with
  | 0 => m
  | S n => S (add n m)
  end.

Lemma test n : even n -> False.
Proof.
  intros H.
  inversion H.
  inv H.

Lemma add_0 n : add n 0 = n.
Proof.
  induction n; simp.
Qed.

Lemma add_S n m : add n (S m) = S (add n m).
Proof.
  induction n; simp.
Qed.