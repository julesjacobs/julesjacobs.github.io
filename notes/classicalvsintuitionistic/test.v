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
  (Γ -> (A -> B) ∧ Δ).
Proof.
  Fail tauto.
Abort.

Lemma to_r_intuitionistic Γ A B :
  (Γ ∧ A -> B) ->
  (Γ -> (A -> B)).
Proof.
  tauto.
Qed.