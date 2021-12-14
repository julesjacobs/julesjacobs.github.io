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

(* Inversion tactic that cleans up the original hypothesis and generated equalities. *)
Ltac inv H := inversion H; clear H; simplify_eq.