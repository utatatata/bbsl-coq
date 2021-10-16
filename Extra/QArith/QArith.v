Require Import Coq.QArith.QArith QOrderedType.

Lemma Qeq_sym_iff : forall x y, x == y <-> y == x.
Proof.
  intros.
  split. q_order. q_order.
Qed.

Lemma Qlt_asym : forall x y, ~(x < y /\ y < x).
Proof.
  unfold not. intros x y H. destruct H.
  q_order.
Qed.

Lemma Qgt_ge_trans : forall x y z, x > y -> y >= z -> x > z.
Proof.
  intros. q_order.
Qed.

Lemma Qge_gt_trans : forall x y z, x >= y -> y > z -> x > z.
Proof.
  intros. q_order.
Qed.

Lemma Qlt_not_ge_iff : forall x y, x < y <-> ~y <= x.
Proof.
  intros. split. q_order. q_order.
Qed.

Lemma Qle_not_gt_iff : forall x y, x <= y <-> ~y < x.
Proof.
  intros. split. q_order. q_order.
Qed.
