Require Import QArith Qminmax.

Lemma Qmin_ltl_comm : forall x y z, Qmin x y < z <-> Qmin y x < z.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_ltr_comm : forall x y z, z < Qmin x y <-> z < Qmin x y.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_lel_comm : forall x y z, Qmin x y <= z <-> Qmin y x <= z.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_ler_comm : forall x y z, z <= Qmin x y <-> z <= Qmin y x.
Proof.
  intros. now rewrite  Q.min_comm.
Qed.

Lemma Qmax_ltl_comm : forall x y z, Qmax x y < z <-> Qmax y x < z.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_ltr_comm : forall x y z, z < Qmax x y <-> z < Qmax y x.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_lel_comm : forall x y z, Qmax x y <= z <-> Qmax y x <= z.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_ler_comm : forall x y z, z <= Qmax x y <-> z <= Qmax y x.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

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
  intros x y z w.
  now rewrite Q.max_lub_iff, Q.min_glb_iff, Q.min_glb_iff.
Qed.
