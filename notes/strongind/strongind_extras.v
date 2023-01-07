From iris.proofmode Require Import tactics.

(* An alternative way of presenting the proof system of the paper
     "Coinduction All the Way Up" by Damien Pous
   Instead of working with the t function, we work with the set Ω = im t.
   Whenever the paper has an element t x,
   we are going to work with y ∈ Ω such that y ≤ x.
   (We will do induction rather than coinduction;
    to convert to coinduction simply flip ≤ and ∪)
*)

Definition set T := T → Prop.

Parameter T:Type.

Parameter le : T → T → Prop.
Notation "x ≤ y" := (le x y).

Axiom le_refl : ∀ x, x ≤ x.
Axiom le_trans : ∀ x y z, x ≤ y → y ≤ z → x ≤ z.
Axiom le_asym : ∀ x y, x ≤ y → y ≤ x → x = y.

Parameter cup : set T → T.
Notation "∪ x" := (cup x) (at level 20).
Axiom le_cup : ∀ (X:set T) y, X y → y ≤ ∪X.
Axiom cup_le : ∀ (X:set T) y, (∀ x, X x → x ≤ y) → ∪X ≤ y.

Parameter f : T → T.

(*
  Initially I tried this:

  Inductive Ω : T → Prop :=
    | Ω_suclim (X:set T) : (∀ x, X x → Ω x) → Ω (f (∪X)).

  But this doesn't work well: when we do induction on Ω we want to separate
  the f-respecting goal from the ∪-respecting goal, because we can usually
  solve the latter goal completely automatically.
*)

Inductive Ω : T → Prop :=
  | Ω_suc x : Ω x → Ω (f x)
  | Ω_lim (X:set T) : (∀ x, X x → Ω x) → Ω (∪X).

Check Ω_ind.
(*
  (∀ x : T, Ω x → P x → P (f x)) →
  (∀ X : set T, (∀ x : T, X x → Ω x) → (∀ x : T, X x → P x) → P (∪ X)) →
  (∀ x : T, Ω x → P x)

  The Ω_suc case says that our goal must respect f,
  and the Ω_lim case says that our goal must respect ∪.
*)

(* This tactic uses induction on Ω and then tries to solve the Ω_lim subgoal automatically. *)
Local Hint Resolve le_refl le_trans le_asym le_cup cup_le Ω_suc Ω_lim : lat.
Ltac induct H := induction H; [|solve [eauto with lat] || eauto 10 with lat].

(* We explicitly have `mono f` assumptions only on the lemmas that need it. *)
Definition mono f := ∀ x y, x ≤ y → f x ≤ f y.

Lemma Ω_incr a : mono f → Ω a → a ≤ f a.
Proof.
  intros ? H. induct H. eauto with lat.
Qed.

Local Hint Resolve Ω_incr : lat.

(* Lemma showing that ∪Ω is a fixed point of f *)
Lemma Ω_fix : mono f → f (∪Ω) = ∪Ω.
Proof.
  eauto 7 using Ω_incr with lat.
Qed.

(* Lemma showing that ∪Ω is the least fixed point of f.
   Instead of "f x = x → ∪Ω ≤ x", we prove the following stronger lemma,
   with ≤ instead of =. This is precisely the Tarski induction principle: *)
Lemma Ω_lfp x : mono f → f x ≤ x → ∪Ω ≤ x.
Proof.
  intros ??. eapply cup_le. intros ? G. induct G. eauto with lat.
Qed.


(* Analogous to the goal "t x ≤ y" is "∀ a, Ω a → a ≤ x → a ≤ y". *)
(* Analogous to the Init rule is "eapply cup_le" on a goal "∪Ω ≤ y". *)
(* Analogous to the Done rule is "assumption" on goal "a ≤ y → a ≤ y". *)
(* Analogous to the CoInd rule is "induct H" on "H :  Ω a". *)

(* Analogous to the Upto rule is using transitivity with `compatible g` *)
Definition compatible g := ∀ x, Ω x → x ≤ g x.
(*
  But I think there is usually no need to define g explicitly.
  Instead, we can state compatibility lemmas directly.
  For instance, for commutativity of bisimilarity we can simply prove:
    ∀ x, Ω x → (a,b) ∈ x → (b,a) ∈ x
  To prove such lemmas, we can use the induct tactic on Ω x.
*)

(* Summary *)
(* ======= *)
(*
  - Instead of several proof rules, we have one proof rule: the induct tactic.
    The other proof rules correspond to normal Coq reasoning.
  - We use induct uniformly to prove goals by coinduction, including compatibility lemmas.
  - The induct tactic works on goals of more general shape than "t x ≤ y".
  - It also sometimes gives a slighly stronger induction hypothesis, because it does not
    hide aready known information behind a guard, like the CoInd rule does.
*)


(* The proof system with the t function from the paper *)
(* =================================================== *)

(* The t function from the paper. *)
(* (Here we use the inductive version of t, so all ≤/∪ are flipped) *)
Definition t x := ∪(λ a, Ω a ∧ a ≤ x).

Definition top := ∪(λ x, True).
Notation "⊤" := top.
Definition cup2 x y := ∪(λ a, a = x ∨ a = y).
Notation "x ∪ y" := (cup2 x y).


(* Proof system from the paper *)

Lemma t_init y : t ⊤ ≤ y → ∪Ω ≤ y.
Proof.
  unfold t, top. intro. eapply le_trans; eauto. eauto with lat.
Qed.

Lemma t_done x y : x ≤ y → t x ≤ y.
Proof.
  intro. eapply cup_le. naive_solver (eauto with lat).
Qed.

Lemma t_ind x y : mono f → f (t (y ∪ x)) ≤ y → t x ≤ y.
Proof.
  unfold cup2, t. intros. eapply le_trans; eauto.
  eapply cup_le. intros ?[G ?]. induct G. eauto 9 with lat.
Qed.

Lemma t_upto g x y :
  compatible g →
  g (t x) ≤ y → t x ≤ y.
Proof.
  assert (Ω (t x)) as G by (constructor; naive_solver).
  induct G. eauto with lat.
Qed.


(* Some other lemmas *)

Lemma Ω_t x : Ω (t x).
Proof.
  constructor. naive_solver.
Qed.

Lemma t_Ω_le x y : t x ≤ y ↔ ∀ a, Ω a → a ≤ x → a ≤ y.
Proof.
  split; unfold t.
  - intros ???G?. eapply le_trans; last done. induct G. eauto with lat.
  - intro. eapply cup_le. intros ?[]. eauto with lat.
Qed.

Lemma t_decr x : t x ≤ x.
Proof.
  eapply cup_le. naive_solver.
Qed.

Lemma Ω_t_incr x : Ω x → x ≤ t x.
Proof.
  unfold t. eauto with lat.
Qed.

Lemma t_compatible g : mono g → compatible g → (∀ x, t x ≤ g x).
Proof.
  eauto using t_decr, Ω_t with lat.
Qed.

Lemma compatible_t g : (∀ x, t x ≤ g x) → compatible g.
Proof.
  unfold compatible. eauto using Ω_t_incr with lat.
Qed.

Lemma t_mono : mono t.
Proof.
  unfold t. intros ???. eapply cup_le. intros ?[]; eauto with lat.
Qed.

Lemma t_init' : t ⊤ = ∪Ω.
Proof.
  eapply le_asym; unfold t, top; eauto with lat.
  eapply cup_le. intros ?[]; eauto with lat.
Qed.



(* The two subgoals we have to prove when we do induction on Ω. *)
Definition cup_closed (P : set T) := ∀ X:set T, (∀ x, X x -> Ω x) -> (∀ x:T, X x → P x) → P (∪X).
Definition f_closed (P : set T) := ∀ x, Ω x -> P x -> P (f x).

(* The induct tactic turns a goal (∀ a, Ω a -> P a) into (f_closed P),
   provided it can solve the second (cup_closed P) subgoal using eauto with lat. *)

(* The following is a basic induction lemma.
   The bi-implication shows that doing the induct tactic doesn't make a goal un-provable,
   provided the second subgoal is solved. *)
Lemma ind P :
  cup_closed P ->
  f_closed P ↔ (∀ a, Ω a -> P a).
Proof.
  intro G.
  split.
  - intros ?? H. induct H. eauto.
  - unfold f_closed. eauto with lat.
Qed.

Lemma ind_param P x :
  cup_closed P ->
  (∀ a, Ω a -> (a ≤ x -> P a) -> (f a ≤ x -> P (f a))) ->
  (∀ a, Ω a -> a ≤ x -> P a).
Proof.
  intros ??? H. induct H. eauto.
Qed.

Lemma ind_param' P x :
  mono f ->
  cup_closed P ->
  (∀ a, Ω a -> P a -> f a ≤ x -> P (f a)) ->
  (∀ a, Ω a -> a ≤ x -> P a).
Proof.
  intros ???? H. induct H. eauto with lat.
Qed.

Lemma ind_param'' P x :
  mono f ->
  cup_closed P ->
  (∀ a, Ω a -> P a -> a ≤ x -> P (f a)) ->
  (∀ a, Ω a -> a ≤ x -> P a).
Proof.
  intros ???? H. induct H. eauto 7 with lat.
Qed.

Lemma cup_closed_true (P : Prop) : P -> cup_closed (λ a, P).
Proof.
  unfold cup_closed. eauto.
Qed.

Lemma cup_closed_le x : cup_closed (λ a, a ≤ x).
Proof.
  unfold cup_closed. eauto with lat.
Qed.

Lemma cup_closed_restrict P x : cup_closed P -> cup_closed (λ a, a ≤ x -> P a).
Proof.
  unfold cup_closed. eauto with lat.
Qed.

Lemma cup_closed_and P Q : cup_closed P -> cup_closed Q -> cup_closed (λ x, P x ∧ Q x).
Proof.
  unfold cup_closed. naive_solver.
Qed.

Lemma cup_closed_forall {A} (P : A -> set T) : (∀ i, cup_closed (P i)) -> cup_closed (λ x, ∀ i, P i x).
Proof.
  unfold cup_closed. eauto.

  Qed.
Lemma cup_closed_or P Q : cup_closed P -> cup_closed Q -> cup_closed (λ x, P x ∨ Q x).
Proof.
  unfold cup_closed.
  intros.
  (* Need classical logic? *)
Abort.

Lemma cup_closed_exists {A} (P : A -> set T) : (∀ i, cup_closed (P i)) -> cup_closed (λ x, ∃ i, P i x).
Proof.
  unfold cup_closed. intros.
  (* Seems false *)
Abort.