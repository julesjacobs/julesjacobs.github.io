(* An alternative way of presenting the proof system of the paper
     "Coinduction All the Way Up" by Damien Pous
  (We will do induction rather than coinduction; to convert to coinduction simply flip ≤ and ∪)

  Main idea
  =========

  Given a monotone function f : T → T, we can define the transfinite sequence of iterates f^α:

    f^(α+1) = f(f^α)
    f^α = ∪{f^β : β < α}

  This sequence is increasing by monotonicity of f, and by a cardinality argument,
  the sequence must eventually stabilise at the least fixed point μf of f.

  Let Ω = {f^α : α ∈ Ord}.        Note: Ω = im t, where t is Pous' function.

  We can prove Ω ⊆ P by transfinite induction:
  - Prove x ∈ P → f(x) ∈ P for all x ∈ Ω
  - Prove X ⊆ P → ∪X ∈ P for all X ⊆ Ω
  From this we can then conclude that μf ∈ P.

  Doing this in Coq is hard, but we can define Ω as an inductive type such that
  its induction principle is precisely that.

  Furthermore, we can define an "induct H" tactic that does the induction,
  and interestingly we can usually prove the ∪-subgoal automatically.
  So if the original goal was:

    H : Ω x
    -------
    P x

  Then after "induct H", if the ∪-subgoal gets solved automatically, the new goal is:

    H : Ω x
    Hind : P x
    ----------
    P (f x)

  To connect this to the paper, whenever the paper has an element t x,
  we are going to work with t ∈ Ω such that t ≤ x.
*)

From iris.proofmode Require Import tactics. (* naive_solver tactic and unicode notations *)

Definition set T := T → Prop.

Parameter L : Type. (* Our lattice *)

Parameter le : L → L → Prop. Notation "x ≤ y" := (le x y).

Axiom le_refl : ∀ x, x ≤ x.
Axiom le_trans : ∀ x y z, x ≤ y → y ≤ z → x ≤ z.
Axiom le_asym : ∀ x y, x ≤ y → y ≤ x → x = y.

Parameter cup : set L → L. Notation "∪ x" := (cup x) (at level 20).

Axiom le_cup : ∀ (X:set L) y, X y → y ≤ ∪X.
Axiom cup_le : ∀ (X:set L) y, (∀ x, X x → x ≤ y) → ∪X ≤ y.

Parameter f : L → L.

(*
  Initially I tried this:

  Inductive Ω : L → Prop :=
    | Ω_step (X:set L) : (∀ x, X x → Ω x) → Ω (f (∪X)).

  But this doesn't work well: when we do induction on Ω we want to separate
  the f-respecting goal from the ∪-respecting goal, because we can usually
  solve the latter goal completely automatically.
*)

Inductive Ω : L → Prop :=
  | Ω_lim (X:set L) : (∀ x, X x → Ω x) → Ω (∪X)
  | Ω_suc x : Ω x → Ω (f x).

Check Ω_ind.
(*
  (∀ x : T, Ω x → P x → P (f x)) →
  (∀ X : set T, (∀ x : T, X x → Ω x) → (∀ x : T, X x → P x) → P (∪ X)) →
  (∀ x : T, Ω x → P x)

  The Ω_suc case says that our goal must respect f,
  and the Ω_lim case says that our goal must respect ∪.
*)

Local Hint Resolve le_refl le_asym le_cup cup_le Ω_suc Ω_lim : lat.
(* Adding le_trans directly to the hint db will be very slow, and it will
   also not solve all goals since then we always recurse on the first subgoal.
   Instead, we do transitivity only when one of the two subgoals is trivially solved. *)
Local Hint Extern 1 (?x ≤ ?y) => eapply le_trans; [by eauto 2|] : lat.
Local Hint Extern 1 (?x ≤ ?y) => eapply le_trans; [|by eauto 2] : lat.
(* This makes the lat tactic very fast, because on a goal ?x ≤ ?y,
   the registered hints only ever create one new subgoal. *)
Ltac lat := by eauto 10 with lat.


(* Demonstrating the lat tactic on some properties of ∪ and ∩ *)

Lemma iff_impl {P Q : set L} : (∀ x, P x ↔ Q x) ↔ (∀ x, P x → Q x) ∧ (∀ x, Q x → P x).
Proof.
  naive_solver.
Qed.

Lemma cup_iff (X:set L) y : y = ∪X ↔ ∀ a, y ≤ a ↔ ∀ x, X x → x ≤ a.
Proof.
  rewrite iff_impl. naive_solver lat.
Qed.

Definition cap (X:set L) := ∪λ y, ∀ x, X x → y ≤ x.
Notation "∩ x" := (cap x) (at level 20).

Lemma cap_le (X:set L) y : X y → ∩X ≤ y.
Proof.
  unfold cap. lat.
Qed.

Lemma le_cap (X:set L) y : (∀ x, X x → y ≤ x) → y ≤ ∩X.
Proof.
  unfold cap. lat.
Qed.

Local Hint Resolve cap_le le_cap : lat.

Lemma cap_iff_unique (X:set L) y : y = ∩X ↔ ∀ a, a ≤ y ↔ ∀ x, X x → a ≤ x.
Proof.
  rewrite iff_impl. naive_solver lat.
Qed.

Notation "⊥" := (∪λ x, False).
Notation "x ∩ y" := (∩λ a, a = x ∨ a = y).

Lemma cap2_le x y z : x ≤ z ∨ y ≤ z → x ∩ y ≤ z.
Proof.
  intros []; eapply le_trans; try apply cap_le; try done; lat.
Qed.

Lemma le_cap2 x y z : z ≤ x → z ≤ y → z ≤ x ∩ y.
Proof.
  intros. eapply le_cap. naive_solver.
Qed.

Local Hint Resolve le_cap2 cap2_le : lat.


(* This tactic uses induction on Ω and then tries to solve the Ω_lim subgoal automatically. *)
Ltac induct H := induction H; [lat|].

(* We explicitly have `mono f` assumptions only on the lemmas that need it. *)
Definition mono f := ∀ x y, x ≤ y → f x ≤ f y.

Lemma Ω_incr x : mono f → Ω x → x ≤ f x.
Proof.
  intros ? O. induct O. lat.
Qed.

(* In certain cases we actually need this lemma for the Ω_lim subgoal. *)
Local Hint Resolve Ω_incr : lat.

(* Lemma showing that ∪Ω is a fixed point of f *)
Lemma Ω_fix : mono f → f (∪Ω) = ∪Ω.
Proof.
  lat.
Qed.

(* Lemma showing that ∪Ω is the least fixed point of f.
   Instead of "f x = x → ∪Ω ≤ x", we prove the following stronger lemma,
   with ≤ instead of =. This is precisely the Tarski induction principle: *)
Lemma Ω_lfp x : mono f → f x ≤ x → ∪Ω ≤ x.
Proof.
  intros ??. eapply cup_le. intros ? O. induct O. lat.
Qed.

(* Comparison with Pous' t-function proof system *)
(* ============================================= *)

(* Analogous to the goal "t x ≤ y" is "∀ a, Ω a → a ≤ x → a ≤ y". *)
(* Analogous to the Init rule is "apply cup_le" on a goal "∪Ω ≤ y". *)
(* Analogous to the Done rule is "assumption" on goal "a ≤ y → a ≤ y". *)
(* Analogous to the CoInd rule is "induct H" on "H : Ω a". *)
(* Analogous to the Upto rule is using transitivity with `compatible g` *)
Definition compatible g := ∀ x, Ω x → x ≤ g x.
(*
  But I think there is usually no need to define g explicitly.
  Instead, we can state compatibility lemmas directly.
  For instance, for commutativity of bisimilarity we can simply prove:
    ∀ x, Ω x → (a,b) ∈ x → (b,a) ∈ x
  To prove such lemmas, we can use the induct tactic on Ω x.
*)

(*
  - Instead of several proof rules, we have one proof rule: the induct tactic.
    The other proof rules correspond to normal Coq reasoning.
  - We can use the induct tactic to prove compatibility lemmas.
  - The induct tactic works on goals that need not be in a particular syntactic shape,
    such as "t x ≤ y", but the lat tactic does need to be able to solve the ∪-subgoal.
  - It sometimes gives a slighly stronger induction hypothesis than the CoInd rule,
    because induct does not hide currently known information behind a guard.
*)


(* Proving the soundness of Pous' t-function proof system using the induct tactic *)
(* ============================================================================== *)

(* The t function from the paper. *)
(* Here we use the inductive version of t, so all ≤/∪ are flipped. *)
Definition t x := ∪λ a, Ω a ∧ a ≤ x.

Notation "⊤" := (∪λ x, True).
Notation "x ∪ y" := (∪λ a, a = x ∨ a = y).

(* Rules of the proof system *)

Lemma t_init y : t ⊤ ≤ y → ∪Ω ≤ y.
Proof.
  unfold t. lat.
Qed.

Lemma t_done x y : x ≤ y → t x ≤ y.
Proof.
  intro. eapply cup_le. naive_solver lat.
Qed.

Lemma t_ind x y : mono f → f (t (y∪x)) ≤ y → t x ≤ y.
Proof.
  unfold t. intros. eapply le_trans; eauto.
  eapply cup_le. intros ?[O ?].
  induct O. naive_solver lat.
Qed.

Lemma t_upto g x y : (∀ x, t x ≤ g x) → g (t x) ≤ y → t x ≤ y.
Proof.
  unfold t. cut (Ω (t x)); [lat|].
  constructor. naive_solver.
Qed.


(* Correspondence *)

Lemma t_Ω_le x y : t x ≤ y ↔ ∀ a, Ω a → a ≤ x → a ≤ y.
Proof.
  unfold t. split.
  - intros ???G. induct G. lat.
  - intro. eapply cup_le. naive_solver lat.
Qed.

Lemma t_compatible g : mono g → compatible g → (∀ x, t x ≤ g x).
Proof.
  intros. eapply cup_le. naive_solver lat.
Qed.

Lemma compatible_t g : (∀ x, t x ≤ g x) → compatible g.
Proof.
  unfold compatible,t. lat.
Qed.


(* Induction principle without assuming monotonicity of f *)
Lemma ind_param x y :
  (∀ a, Ω a → (a ≤ x → a ≤ y) → (f a ≤ x → f a ≤ y)) →
  (∀ a, Ω a → a ≤ x → a ≤ y).
Proof.
  intros ?? H. induct H. eauto.
Qed.

(* If f is monotone, then we can automatically take care of the (a ≤ x) precondition *)
Lemma ind_param' x y :
  mono f →
  (∀ a, Ω a → a ≤ y → f a ≤ x → f a ≤ y) →
  (∀ a, Ω a → a ≤ x → a ≤ y).
Proof.
  intros ??? H. induct H. lat.
Qed.

(* Weaker induction principle that hides already known info behind a guard *)
(* This corresponds to the CoInd principle from the paper *)
Lemma ind_weak x y :
  mono f →
  (∀ a, Ω a → a ≤ y∩x → f a ≤ y) →
  (∀ a, Ω a → a ≤ x → a ≤ y).
Proof.
  intros ??? H. induct H. lat.
Qed.



(* Some other lemmas about t *)

Lemma t_decr x : t x ≤ x.
Proof.
  unfold t. eapply cup_le. naive_solver.
Qed.

Lemma Ω_t x : Ω (t x).
Proof.
  constructor. naive_solver.
Qed.

(* This is the most important lemma bout t and f *)
Lemma ft_incr x : mono f → t x ≤ f (t x).
Proof.
  intro Hx. induct (Ω_t x). lat.
Qed.

Local Hint Resolve Ω_t t_decr ft_incr : lat.

Lemma t_mono : mono t.
Proof.
  intros ???. eapply le_cup. lat.
Qed.

Local Hint Resolve t_mono : lat.



(* Cup-closed *)

Definition cup_closed (P : set L) := ∀ X:set L, (∀ x, X x → Ω x) → (∀ x, X x → P x) → P (∪X).

Lemma cup_closed_true (P : Prop) : P → cup_closed (λ a, P).
Proof.
  unfold cup_closed. eauto.
Qed.

Lemma cup_closed_le x : cup_closed (λ a, a ≤ x).
Proof.
  unfold cup_closed. lat.
Qed.

Lemma cup_closed_and P Q : cup_closed P → cup_closed Q → cup_closed (λ x, P x ∧ Q x).
Proof.
  unfold cup_closed. naive_solver.
Qed.

Lemma cup_closed_forall {A} (P : A → set L) : (∀ i, cup_closed (P i)) → cup_closed (λ x, ∀ i, P i x).
Proof.
  unfold cup_closed. eauto.
Qed.

Lemma cup_closed_mono g : mono g → cup_closed (λ x, x ≤ g x).
Proof.
  unfold cup_closed. lat.
Qed.

Lemma cup_closed_impl (P Q : set L) : (∀ x y, P x → y ≤ x → P y) → cup_closed Q → cup_closed (λ a, P a → Q a).
Proof.
  unfold cup_closed. lat.
Qed.

Require Import Logic.Classical.

Lemma cup_closed_or P Q : cup_closed P → cup_closed Q → cup_closed (λ x, P x ∨ Q x).
Proof.
  intros HP HQ X HΩ HPQ.
  unfold cup_closed in *.
  classical_left.
Admitted.

Definition f_closed (P : set L) := ∀ x, Ω x → P x → P (f x).

(* The induct tactic turns a goal (∀ a, Ω a → P a) into (f_closed P),
   provided it can solve the second (cup_closed P) subgoal using eauto with lat. *)

(* The following is a basic induction lemma.
   The bi-implication shows that doing the induct tactic doesn't make a goal un-provable,
   provided the second subgoal is solved. *)
Lemma ind P :
  cup_closed P →
  f_closed P ↔ (∀ a, Ω a → P a).
Proof.
  intro G.
  split.
  - intros ?? H. induct H. eauto.
  - unfold f_closed. eauto with lat.
Qed.

Lemma ind_param0 P x :
  cup_closed P →
  (∀ a, Ω a → (a ≤ x → P a) → (f a ≤ x → P (f a))) →
  (∀ a, Ω a → a ≤ x → P a).
Proof.
  intros ??? H. induct H. eauto.
Qed.

Lemma ind_param0' P x :
  mono f →
  cup_closed P →
  (∀ a, Ω a → P a → f a ≤ x → P (f a)) →
  (∀ a, Ω a → a ≤ x → P a).
Proof.
  intros ???? H. induct H. eauto with lat.
Qed.

Lemma ind_weak0 P x :
  mono f →
  cup_closed P →
  (∀ a, Ω a → P a → a ≤ x → P (f a)) →
  (∀ a, Ω a → a ≤ x → P a).
Proof.
  intros ???? H. induct H. eauto 7 with lat.
Qed.



(* Correspondence between t induction principles and Ω induction principles *)

Lemma corr x y : t x ≤ y ↔ ∀ a, Ω a → a ≤ x → a ≤ y.
Proof.
  split; [unfold t|]; lat.
Qed.

Lemma corr' x y : mono f → f (t (y ∩ x)) ≤ y ↔ ∀ a, Ω a → a ≤ y∩x → f a ≤ y.
Proof.
  split; [unfold t|]; lat.
Qed.

Lemma corr'_alt x y : (∀ a, Ω a → a ≤ y∩x → f a ≤ y) ↔ (∀ a, Ω a → a ≤ y → a ≤ x → f a ≤ y).
Proof.
  split; lat.
Qed.

Lemma t_ind_alt_pf_fixed x y : mono f → f (t (y ∩ x)) ≤ y → t x ≤ y.
Proof.
  intro. rewrite corr corr' //. eauto using ind_weak.
Qed.

Lemma cup_cap x y z : x ≤ y ∩ z → x ∩ y ≤ z.
Proof.
  lat.
Qed.

(* I think the ↔ version of this lemma holds too, but I don't know how to prove it
   without applealing to the ordinal sequence. *)
Lemma corr'' x y : mono f → f (t (y ∩ x)) ∩ t x ≤ y → ∀ a, Ω a → a ≤ y → f a ≤ x → f a ≤ y.
Proof.
  intros Hf G ????. eapply le_trans; last exact G. unfold t. eauto 20 with lat.
Qed.

Lemma t_ind_strong_pf_fixed x y : mono f → f (t (y ∩ x)) ∩ t x ≤ y → t x ≤ y.
Proof.
  intros.
  eapply corr. eapply ind_param'; eauto.
  eapply corr''; eauto.
Qed.

Lemma check_no_loss x y : mono f → x ≤ y → t x ≤ y.
Proof.
  intros. eapply t_ind_strong_pf_fixed; eauto.
  eapply cap2_le. right. by eapply t_done.
Qed.

Require Import Logic.Classical.

Lemma cmp x y : mono f → Ω x → Ω y → x ≤ y ∨ f y ≤ x.
Proof.
  intros Hf Ωx. revert y. induction Ωx; intros y Ωy.
  - classical_left. eapply cup_le. naive_solver lat.
  - classical_right. eapply Hf. induct Ωy. naive_solver lat.
Qed.

Print cup_closed.

Lemma cup_closed_disj y z (X:set L) :
  (∀ x, X x → x ≤ y ∨ z ≤ x) → ∪X ≤ y ∨ z ≤ ∪X.
Proof.
  intro. classical_left. eapply cup_le. naive_solver lat.
Qed.

Lemma cup_closed_disj' y z (X:set L) :
  (∀ x, X x → z ≤ x ∨ x ≤ y) → z ≤ ∪X ∨ ∪X ≤ y.
Proof.
  intros. rewrite comm. eapply cup_closed_disj. naive_solver.
Qed.

Local Hint Resolve cup_closed_disj cup_closed_disj' : lat.

Lemma disjL {A A' B : Prop} : (A → A') → A ∨ B → A' ∨ B.
Proof. naive_solver. Qed.

Lemma disjR {A B B' : Prop} : (B → B') → A ∨ B → A ∨ B'.
Proof. naive_solver. Qed.

Lemma cmp' x y : mono f → Ω x → Ω y → x ≤ y ∨ f y ≤ x.
Proof.
  intros Hf Ωx. revert y. induct Ωx. intros y Ωy.
  apply (disjR (Hf _ _)). induct Ωy. naive_solver.
Qed.

Lemma corr''_iff x y : mono f → f (t (y ∩ x)) ∩ t x ≤ y ↔ ∀ a, Ω a → a ≤ y → f a ≤ x → f a ≤ y.
Proof.
  split; eauto using corr''. intros.
  destruct (cmp (t x) (t y)); try lat.
  eapply cap2_le. left.
  eapply le_trans; last eapply (H0 (t y)); lat.
Qed.