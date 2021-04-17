From iris.proofmode Require Import tactics.

Definition N := ∀ t : Set, (t -> t) -> (t -> t).

Definition z : N := λ _ f z, z.
Definition s (n : N) : N := λ _ f z, f (n _ f z).

Definition add (n m : N) : N := λ _ f, n _ f ∘ m _ f.
Definition mul (n m : N) : N := λ _ f, n _ (m _ f).
Definition pow (n m : N) : N := λ _, n _ (m _).

Definition two := s (s z).
Definition four := add two two.
Definition four' := mul two two.
Definition four'' := pow two two.

Compute four.
Compute four'.
Compute four''.

Definition f (g : N -> N) (k : N) : N -> N :=
    k (N -> N) (λ f n, n N f n) g.

Compute (f s (s (s z)) two).