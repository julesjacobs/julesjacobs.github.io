From Coq Require Import Lia.

Lemma strong_induction (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros H n.
  eapply H.
  induction n.
  - lia.
  - intros m Hm.
     eapply H.
     intros k Hk.
     eapply IHn. lia.
Qed.