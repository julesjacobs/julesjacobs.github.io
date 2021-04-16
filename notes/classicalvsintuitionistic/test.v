From iris.proofmode Require Import tactics.

Lemma cut (Γ Δ Σ Π A : Prop) :
  (Γ -> (Δ ∨ A)) ->
  ((A ∧ Σ) -> Π) ->
  ((Γ ∧ Σ) -> (Δ ∨ Π)).
Proof.
  tauto.
Qed.

Lemma to_l (Γ Δ Σ Π A B : Prop) :
  (Γ -> (A ∨ Δ)) ->
  ((Σ ∧ B) -> Π) ->
  ((Γ ∧ Σ ∧ (A -> B)) -> (Δ ∨ Π)).
Proof.
  tauto.
Qed.

Lemma cut2 (Γ Δ Σ Π A : Prop) :
  (Γ -> (Δ ∨ A)) ->
  ((Γ ∧ A) -> Π) ->
  (Γ -> (Δ ∨ Π)).
Proof.
  tauto.
Qed.

(*
Gentzen's cut rule: when we want to prove a disjunction, we can cut along a proposition A.
Coq's ordinary cut is the special case when Δ = False.
*)

Lemma cut2_coq (Γ Δ Σ Π A : Prop) :
  (Γ -> A) ->
  ((Γ ∧ A) -> Π) ->
  (Γ -> Π).
Proof.
  tauto.
Qed.

Lemma to_r_classical Γ Δ A B :
  (Γ ∧ A -> B ∨ Δ) ->
  (Γ -> (A -> B) ∨ Δ).
Proof.
  Fail tauto.
Abort.

Lemma to_r_classical' Γ Δ A B :
  (∀ P, ¬ ¬ P -> P) ->
  (Γ ∧ A -> B ∨ Δ) ->
  (Γ -> (A -> B) ∨ Δ).
Proof.
  intros dn??. apply dn. tauto.
Qed.

Lemma to_r_intuitionistic Γ A B :
  (Γ ∧ A -> B) ->
  (Γ -> (A -> B)).
Proof.
  tauto.
Qed.

(* We can still apply this principle if Δ is decidable. *)

Lemma to_r_classical'' Γ Δ A B :
  (Δ ∨ ¬ Δ) ->
  (Γ ∧ A -> B ∨ Δ) ->
  (Γ -> (A -> B) ∨ Δ).
Proof.
  tauto.
Qed.

Lemma to_r_classical''' Γ Δ A B :
  (¬ ¬ Δ -> Δ) ->
  (Γ ∧ A -> B ∨ Δ) ->
  (Γ -> (A -> B) ∨ Δ).
Proof.
  Fail tauto.
Abort.

(*
A goal B is classical if ¬ ¬ B -> B.

Decidable propositions are classical, but not all classical propositions are decidable.

We can apply classical principles if our goal is classsical.
*)

Lemma dn_goal (A B : Prop) :
  (A -> ¬ ¬ B) ->
  (¬ ¬ A -> ¬ ¬ B).
Proof.
  tauto.
Qed.

Lemma dn_goal' (A B : Prop) :
  ((A ∨ ¬ A) -> ¬ ¬ B) ->
  (¬ ¬ B).
Proof.
  tauto.
Qed.

Definition classical (P : Prop) := ¬ ¬ P -> P.
Definition decidable (P : Prop) := P ∨ ¬ P.

Lemma dc P :
  decidable P -> classical P.
Proof.
  unfold decidable,classical. tauto.
Qed.

Lemma cd P :
  classical P -> decidable P.
Proof.
  unfold decidable,classical. Fail tauto.
Abort.

(* What about quantifiers though? Need to look into double negation translation for them.*)