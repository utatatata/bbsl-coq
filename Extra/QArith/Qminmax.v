Require Import Coq.QArith.QArith Coq.QArith.Qminmax.

(** To use q_order, a set of shortcuts for converting qmin, qmax into comparison relations. **)

Lemma Qmin_lt_max_iff : forall x y z w, Qmin x y < Qmax z w <-> (x < z \/ x < w) \/ y < z \/ y < w.
Proof.
  intros.
  now rewrite Q.min_lt_iff, Q.max_lt_iff, Q.max_lt_iff.
Qed.

Lemma Qmin_le_max_iff : forall x y z w, Qmin x y <= Qmax z w <-> (x <= z \/ x <= w) \/ y <= z \/ y <= w.
Proof.
  intros.
  now rewrite Q.min_le_iff, Q.max_le_iff, Q.max_le_iff.
Qed.

Lemma Qmax_lt_min_iff : forall x y z w, Qmax x y < Qmin z w <-> (x < z /\ x < w) /\ y < z /\ y < w.
Proof.
  intros.
  now rewrite Q.max_lub_lt_iff, Q.min_glb_lt_iff, Q.min_glb_lt_iff.
Qed.

Lemma Qmax_le_min_iff : forall x y z w, Qmax x y <= Qmin z w <-> (x <= z /\ x <= w) /\ y <= z /\ y <= w.
Proof.
  intros.
  now rewrite Q.max_lub_iff, Q.min_glb_iff, Q.min_glb_iff.
Qed.
