(* Introduction to Coq *)

(* 
  In this lecture, we learn how to do proofs with propositional logical connectives:
    False
    True
    P /\ Q (and)
    P \/ Q (or)
    ~P (not)

  We then show how all these connectives can be encoded using only forall and ->.
*)

(* In this lecture, we will  *)

Lemma False_example (P : Prop) : False -> P.
Proof.
  intros.
  destruct H.
Qed.

Lemma True_example (P : Prop) : P -> P /\ True.
Proof.
  intros.
  split.
  apply H.
  constructor.
Qed.

Lemma And_example (P Q : Prop) : P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Lemma Or_example (P Q R : Prop) : P \/ Q -> (P -> R) /\ (Q -> R) -> R.
Proof.
  intros HOr HAnd.
  destruct HAnd as [HPR HQR].
  destruct HOr.
  - apply HPR.
    apply H.
  - apply HQR.
    apply H.
Qed.

Lemma Not_example (P Q : Prop) : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  - unfold not.
    intros HP.
    apply H.
    left.
    apply HP.
  - unfold not.
    intros HQ.
    apply H.
    right.
    apply HQ.
Qed.

Lemma Not_non_example (P Q : Prop) : ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros.
  left.
  intros HP.
  apply H.
  split.
  apply HP.
  (* We cannot prove this in Coq! This lemma is not constructively valid. *)
Abort.

(* We can prove it if we assume the law of excluded middle. *)
Axiom excluded_middle : forall (P : Prop), P \/ ~P.

Lemma Not_non_example' (P Q : Prop) : ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  (* Exercise! *)
Admitted.


(* We now define the logical connectives using only forall and ->. *)

Definition Fals := forall (P : Prop), P.

Lemma ex_falso_quodlibet (P : Prop) : Fals -> P.
Proof.
  unfold Fals.
  intros H.
  apply H.
Qed.

Lemma Fals_correct : Fals <-> False.
Proof.
  split.
  - intros H.
    apply H.
  - intros H.
    destruct H.
Qed.

Definition not (P : Prop) : Prop := P -> Fals.

Definition Tru := not Fals.

Lemma Tru_intro : Tru.
Proof.
  unfold Tru.
  unfold not.
  intros H.
  apply H.
Qed.

Lemma Tru_correct : Tru <-> True.
Proof.
  split.
  - intros H.
    constructor.
  - intros H.
    apply Tru_intro.
Qed.
    
Definition and (P Q : Prop) : Prop := forall (R : Prop), (P -> Q -> R) -> R.

Lemma and_elim_left P Q : and P Q -> P.
Proof.
  intros H.
  unfold and in H.
  apply H.
  intros H1 H2.
  apply H1.
Qed.

Lemma and_elim_right P Q : and P Q -> Q.
Proof.
  intros H.
  unfold and in H.
  apply H.
  intros H1 H2.
  apply H2.
Qed.

Lemma and_intro P Q : P -> Q -> and P Q.
Proof.
  intros HP HQ.
  unfold and.
  intros R H.
  apply H.
  - exact HP.
  - exact HQ.
Qed.

Lemma and_comm P Q : and P Q -> and Q P.
Proof.
  intros H.
  apply and_intro.
  - apply (and_elim_right P Q). apply H.
  - apply (and_elim_left P Q). apply H.
Qed.

Lemma and_correct (P Q : Prop) : and P Q <-> P /\ Q.
Proof.
  split.
  - intros H.
    split.
    + apply (and_elim_left P Q H).
    + apply (and_elim_right P Q H).
  - intros H.
    destruct H as [HP HQ].
    apply and_intro.
    + apply HP.
    + apply HQ.
Qed.


(* We can define our own tactics similar to the built-in tactics *)
Ltac destruct_and H :=
  pose proof (and_elim_left _ _ H) as H1;
  pose proof (and_elim_right _ _ H) as H2;
  clear H.

Ltac split_and := apply and_intro.

Lemma and_comm' P Q : and P Q -> and Q P.
Proof.
  intros H.
  destruct_and H.
  split_and.
  - apply H2.
  - apply H1.
Qed.


Definition or (P Q : Prop) : Prop := forall (R : Prop), (P -> R) -> (Q -> R) -> R.

Lemma or_intro_left P Q : P -> or P Q.
Proof.
  intros HP.
  unfold or.
  intros R H1 H2.
  apply H1.
  apply HP.
Qed.

Lemma or_intro_right P Q : Q -> or P Q.
Proof.
  intros HQ.
  unfold or.
  intros R H1 H2.
  apply H2.
  apply HQ.
Qed.

Lemma or_elim P Q (R : Prop) : or P Q -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros HPQ H1 H2.
  unfold or in HPQ.
  apply HPQ.
  - apply H1.
  - apply H2.
Qed.

Lemma or_correct P Q : or P Q <-> P \/ Q.
Proof.
  (* Exercise *)
Admitted.

(* Bonus: encoding equality à la Leibniz *)

Definition eq (T : Type) (x : T) (y : T) : Prop := forall (P : T -> Prop), P x -> P y.

Lemma eq_refl (T : Type) (x : T) : eq T x x.
Proof.
  intros P H.
  apply H.
Qed.

Lemma eq_sym (T : Type) (x y : T) : eq T x y -> eq T y x.
Proof.
  intros H.
  apply H.
  apply eq_refl.
Qed.

Lemma eq_trans (T : Type) (x y z : T) : eq T x y -> eq T y z -> eq T x z.
Proof.
  intros H1 H2.
  apply H2.
  apply H1.
Qed.

Lemma eq_correct (T : Type) (x y : T) : eq T x y <-> x = y.
Proof.
  (* Exercise *)
Admitted.


(* Actually, implication (->) is a special case of forall! *)

Definition imp (P Q : Prop) : Prop := forall H : P, Q.

Lemma imp_correct (P Q : Prop) : imp P Q <-> (P -> Q).
Proof.
  unfold imp.
  (* Coq already prints the forall as ->. *)
  (* Implication is *literally* just a forall! *)
  split.
  - intros H. apply H.
  - intros H. apply H.
Qed.


(* 
  In Coq, the connectives are not defined in terms of forall, but in terms of Inductive types. 
  An inductive type lists all the constructors that make up the type.
  For propositions, this means that it lists all the ways to prove the proposition.
*)

(* There are no ways to prove False. *)
Inductive False' : Prop := .

(* There is one way to prove True. *)
Inductive True' : Prop :=
  | I : True'. (* I is the constructor for True' *)

(* To prove and P Q, we need to provide a proof of P and a proof of Q. *)
Inductive and' (P Q : Prop) : Prop :=
  | conj : P -> Q -> and' P Q. (* conj is the constructor for and' *)

(* To prove or P Q, we need to provide a proof of P or a proof of Q. *)
Inductive or' (A B : Prop) : Prop :=
  | or_introl : A -> or' A B (* or_introl is the constructor for proving or' from A *)
  | or_intror : B -> or' A B. (* or_intror is the constructor for proving or' from B *)

(* Equality is a more complex example. *)
(* The only way to prove eq' T x y is if x and y are the same. *)
Inductive eq' (T : Type) (x : T) : T -> Prop :=
  | eq_refl' : eq' T x x. (* eq_refl' is the constructor for eq' *)

(* 
  These inductive types are manipulated with two tactics:
  - destruct: do case analysis on the inductive type
  - apply [constructor_name]: apply the constructor to prove the type
    (we can also use `constructor i` for the i-th constructor, 
    or simply `constructor` to apply the first matching constructor)
*)

Lemma and_comm'' P Q : and' P Q -> and' Q P.
Proof.
  intros H.
  destruct H as [HP HQ].
  constructor. (* We can also use `apply conj` here. For the built-in conjunction, we can use `split` *)
  - apply HQ.
  - apply HP.
Qed.

Lemma or_comm'' P Q : or' P Q -> or' Q P.
Proof.
  intros H.
  destruct H as [HP | HQ].
  - constructor 2. apply HP.
  - constructor 1. apply HQ.
Qed.

Lemma eq_comm'' (T : Type) (x y : T) : eq' T x y -> eq' T y x.
Proof.
  intros H.
  destruct H.
  apply eq_refl'.
Qed.