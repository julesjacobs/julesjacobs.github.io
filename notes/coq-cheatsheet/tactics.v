(* Simplifies equations by doing substitution and injection. *)
Tactic Notation "simplify_eq" := repeat match goal with
  | _ => congruence || (progress subst)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  end.

(* Inversion tactic that cleans up the original hypothesis and generated equalities. *)
Ltac inv H := inversion_clear H; simplify_eq.

Ltac simp := repeat match goal with
  | H : False |- _ => destruct H
  | H : ex _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | H : _ * _ |- _ => destruct H
  | H : ?P -> ?Q, H2 : ?P |- _ => specialize (H H2)
  | |- forall x,_ => intro
  | _ => progress (simpl in *; simplify_eq)
  | _ => solve [eauto]
  end.

Ltac cases := repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  | |- _ /\ _ => split
  | |- context[if ?x then _ else _] => destruct x eqn:?
  | |- context[match ?x with _ => _ end] => destruct x eqn:?
  | H : context[if ?x then _ else _] |- _ => destruct x eqn:?
  | H : context[match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.