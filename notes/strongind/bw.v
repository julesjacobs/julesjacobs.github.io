Require Import Setoid Morphisms Basics.
Require Import ssreflect ssrfun ssrbool.
Require Import Classical.

Set Implicit Arguments.


Parameter C: Type.
Parameter leq: relation C.
Infix "<=" := leq (at level 70).
Parameter PreOrder_leq: PreOrder leq.
Parameter antisym: forall x y, x <= y -> y <= x -> x = y.
#[export] Existing Instance PreOrder_leq.
#[export] Hint Extern 0 => reflexivity: core.
#[export] Instance rew_leq: RewriteRelation leq := {}.


Parameter sup: (C -> Prop) -> C.
Parameter sup_spec: forall P z, sup P <= z <-> forall x, P x -> x <= z.

Implicit Types x y z c: C.
Implicit Types P Q: C -> Prop.

Lemma leq_sup: forall P x, P x -> x <= sup P.
Proof. now intros ??; apply sup_spec. Qed.
#[export] Hint Resolve leq_sup: core.

Lemma eq_leq: forall x y, x = y -> x <= y.
Proof. by move=>??<-. Qed.

Definition sup_closed P := forall Q, (forall x, Q x -> P x) -> P (sup Q).

Definition choose x y := forall P, (forall p, P p -> p <= x \/ y <= p) -> sup P <= x \/ y <= sup P.
(* a weak consequence of EM *)
Lemma choose1: forall x y, x <= y -> choose x y.
Proof.
  move=>x y xy P HP.
  classical_left. apply sup_spec=>z Pz. case: (HP z Pz)=>//yz.
  contradict H. rewrite yz; auto.
Qed.
(* a possibly even weaker one *)
Lemma choose2: forall x, choose x x.
Proof. intro. by apply choose1. Qed.
Lemma choose2': forall x P, (forall p, P p -> p <= x \/ x <= p) -> sup P <= x \/ exists z, P z /\ x <= z.
Proof.                          (* stronger than choose2? *)
  move=>x P HP.
  classical_left. apply sup_spec=>z Pz. case: (HP z Pz)=>//yz.
  contradict H. eauto.
Qed.


Parameter f: C -> C.
Parameter tower: forall P, sup_closed P -> (forall x, P x -> P (f x)) -> forall x, P x.

Section s.
  Hypothesis Hf: forall x, x <= f x.
  Theorem strong_chain: forall x y, x <= y \/ f y <= x.
  Proof.
   (* essentially your (Jules) proof *)
   apply: tower.
   - intros T IH c. by apply choose1; auto.
   - intros x IHx y.
     have H: f x <= y \/ y <= x. {
       revert y. apply: tower.
       -- move=>T IH. rewrite or_comm. apply choose1=>//c Tc. rewrite or_comm; auto.
       -- move=>y IHy. case: (IHx y); auto=>xy. left.
          case: IHy=>yx. by rewrite yx.
          apply eq_leq; f_equal; by apply antisym.
     }
     case: H; auto=>yx. right. case: (IHx y)=>xy.
     by apply eq_leq, f_equal, antisym.
     by rewrite xy.
  Qed.
  (* is there a more direct proof of this corollary? *)
  Corollary ext_implies_mon: Proper (leq ==> leq) f.
  Proof.
    move=>x y xy. case: (strong_chain y x)=>yx.
    by apply eq_leq, f_equal, antisym.
    by rewrite yx.
  Qed.
End s.

Section t.
  (* a stronger hypothesis *)
  Hypothesis Hf: Proper (leq ==> leq) f.
  Lemma mon_implies_ext: forall x, x <= f x.
  Proof.
    apply: tower.
    - move=>Q HQ. apply sup_spec=>x Qx. rewrite (HQ _ Qx). by apply Hf; auto.
    - intros. by apply Hf.
  Qed.
  Lemma leq_next: forall x y, (forall z, f z <= x -> z <= y) -> x <= f y.
  Proof.
    apply: tower.
    - move=>T IH y H. apply sup_spec=>x Tx. apply IH=>//z zx.
      apply H. rewrite zx; auto.
    - move=>x IH y H. by apply Hf, H.
  Qed.
  (* yielding a weaker result, but using less classical logic ([choose2] vs [choose1])*)
  Lemma mon_implies_chain: forall x y, x <= y \/ y <= x.
  Proof.
    apply: tower.
    - intros T IH y. by apply choose2; auto.
    - intros x IH y.
      case: (@choose2 x (fun t => f t <= y))=>[c _|H|H].
      by generalize (IH c); tauto.
      right. apply leq_next=>z Hz. by rewrite -H; auto.
      left.                     (* not clear... *)

   Restart.
   apply: tower.
    - intros T IH y. by apply choose2; auto.
    - intros x IH y.
      case: (@choose2' x (fun t => f t <= y))=>[c _|H|[z [yz xz]]].
      by generalize (IH c); tauto.
      right. apply leq_next=>z Hz. by rewrite -H; auto.
      left. by rewrite xz.
  Qed.
End t.
