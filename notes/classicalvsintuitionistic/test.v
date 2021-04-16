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