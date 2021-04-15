From iris.proofmode Require Import tactics.

Inductive leq : (nat * nat) -> Prop :=
  | leq_zero : leq (0,0)
  | leq_succ1 n m : leq (n,m) -> leq (n, S m)
  | leq_succ n m : leq (n,m) -> leq (S n, S m).

Check leq_ind.

Inductive leq_type : (nat * nat) -> Type :=
  | leq_zero' : leq_type (0,0)
  | leq_succ1' n m : leq_type (n,m) -> leq_type (n, S m)
  | leq_succ' n m : leq_type (n,m) -> leq_type (S n, S m).

Check leq_type_ind.

Definition T:Type := (nat * nat).

Definition set (T : Type) := T -> Prop.

Definition subset (A B : set T) := ∀ x, A x -> B x.
Definition intersection (P : set (set T)) := λ x, ∀ A, P A -> A x.
Definition lfp (F : set T -> set T) := intersection (λ A, subset (F A) A).

Definition F : set (nat * nat) -> set (nat * nat) :=
  λ A, λ '(n,m), (n = 0 ∧ m = 0) ∨
          (∃ m', m = S m' ∧ A (n,m')) ∨
          (∃ n' m', n = S n' ∧ m = S m' ∧ A (n',m')).

Definition leq' := lfp F.

Lemma leq_leq' n m :
  leq (n,m) <-> leq' (n,m).
Proof.
  unfold leq', lfp, intersection, subset, F. split.
  - induction 1; naive_solver.
  - intros H. apply (H leq). intros [].
    naive_solver (eauto using leq).
Qed.