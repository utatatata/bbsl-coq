Require Import QArith QOrderedType Qminmax.
Require Import Extra.Init.Logic Extra.QArith.QArith Extra.QArith.Qminmax.

Local Open Scope Q_scope.


Definition Interval : Type := Q * Q.

Declare Scope Interval_scope.
Open Scope Interval_scope.

Definition lower : Q * Q -> Q := fst.
Definition upper : Q * Q -> Q := snd.
Definition Iin (x : Q) (i : Interval) := lower i <= x <= upper i.
Definition Inin (x : Q) (i : Interval) := x < lower i \/ upper i < x.
Definition Iempty (i : Interval) := lower i > upper i.
Definition Inempty (i :Interval) := lower i <= upper i.

Lemma Iempty_not_nempty_iff : forall i, Iempty i <-> ~Inempty i.
Proof.
  unfold Iempty, Inempty. intro.
  split. q_order. q_order.
Qed.

Lemma Inempty_not_empty_iff : forall i, Inempty i <-> ~Iempty i.
Proof.
  unfold Inempty, Iempty. intro.
  split. q_order. q_order.
Qed.

Lemma Iempty_nempty_dec : forall i, {Iempty i} + {Inempty i}.
Proof.
  unfold Iempty, Inempty. intro.
  apply Qlt_le_dec.
Qed.

Lemma Iin_not_nin_iff : forall x i, Inempty i -> Iin x i <-> ~Inin x i.
Proof.
  unfold Inempty, Iin, Inin. intros x i H. split.
  - intros H0 H1. destruct H0, H1. q_order. q_order.
  - intros H0. apply nor_nandn in H0. destruct H0.
    split. q_order. q_order.
Qed.

Lemma Inin_not_in : forall x i, Inempty i -> Inin x i -> ~Iin x i.
Proof.
  unfold Inempty, Inin, Iin.
  intros x i H H0 H1. destruct H1, H0.
  q_order. q_order.
Qed.

(* Lemma Inot_in_nin : forall x i, Inempty i -> ~Iin x i -> Inin x i
 * need classical facts
 *)

Lemma Iin_lower : forall i, Inempty i -> Iin (lower i) i.
Proof.
  unfold Inempty, Iin. intros.
  split. apply Qle_refl. assumption.
Qed.

Lemma Iin_upper : forall i, Inempty i -> Iin (upper i) i.
Proof.
  unfold Inempty, Iin. intros.
  split. assumption. apply Qle_refl.
Qed.

Definition width (i : Interval) := Qmax 0 (upper i - lower i).

Definition Ieq (i j : Interval) := lower i == lower j /\ upper i == upper j.
Definition Ilt (i j : Interval) := upper i < lower j.
Definition Ile (i j : Interval) := upper i <= lower j.
Notation Igt a b := (Ilt b a) (only parsing).
Notation Ige a b := (Ile b a) (only parsing).

Infix "==" := Ieq (at level 70, no associativity) : Interval_scope.
Infix "<" := Ilt : Interval_scope.
Infix "<=" := Ile : Interval_scope.
Notation "x > y" := (Ilt y x)(only parsing) : Interval_scope.
Notation "x >= y" := (Ile y x)(only parsing) : Interval_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Interval_scope.

Lemma Ieq_refl : forall i, i == i.
Proof.
  unfold Ieq. intros. split. q_order. q_order.
Qed.

Lemma Ieq_sym_iff : forall i j, i == j <-> j == i.
Proof.
  destruct i as (il, iu), j as (jl, ju).
  unfold Ieq. simpl.
  now rewrite (Qeq_sym_iff jl il), (Qeq_sym_iff ju iu).
Qed.

Lemma Ieq_trans : forall i j k, i == j -> j == k -> i == k.
Proof.
  unfold Ieq.
  intros i j k H H0. destruct H, H0.
  split. q_order. q_order.
Qed.

Lemma Ilt_antisymm : forall i j, Inempty i -> Inempty j -> i < j -> ~j < i.
Proof.
  unfold Inempty, Ilt.
  q_order.
Qed.

Lemma Igt_antisymm : forall i j, Inempty i -> Inempty j -> i > j -> ~j > i.
Proof.
  unfold Inempty, Ilt.
  q_order.
Qed.

Lemma Ilt_not_gt : forall i j,
  Inempty i -> Inempty j -> i < j -> ~i > j.
Proof.
  unfold Inempty, Ilt.
  q_order.
Qed.

Lemma Igt_not_lt : forall i j,
  Inempty i -> Inempty j -> i > j -> ~i < j.
Proof.
  unfold Inempty, Ilt.
  q_order.
Qed.

Lemma Ile_trans : forall i j k, Inempty j -> i <= j -> j <= k -> i <= k.
Proof.
  unfold Ile, Inempty.
  q_order.
Qed.

Lemma Ilt_trans : forall i j k, Inempty j -> i < j -> j < k -> i < k.
Proof.
  unfold Ilt, Inempty.
  q_order.
Qed.

Lemma Ilt_irrefl : forall i, Inempty i -> ~i < i.
Proof.
  unfold Ilt, Inempty.
  q_order.
Qed.

Definition Iintersection (i j : Interval) : Interval :=
  (Qmax (lower i) (lower j), Qmin (upper i) (upper j)).

Lemma Iintersection_comm : forall i j, Iintersection i j == Iintersection j i.
Proof.
  unfold Iintersection, Ieq.
  simpl. intros.
  rewrite Q.max_comm, Q.min_comm.
  split. q_order. q_order.
Qed.

Definition Isubset (i j : Interval) := (lower j < lower i)%Q /\ (upper i < upper j)%Q.
Definition Isubseteq (i j : Interval) := (lower j <= lower i)%Q /\ (upper i <= upper j)%Q.
Notation Isupset a b := (Isubset b a) (only parsing).
Notation Isupseteq a b := (Isubseteq b a) (only parsing).

Lemma Isubseteq_refl : forall x, Isubseteq x x.
Proof.
  unfold Isubseteq. intros.
  split. q_order. q_order.
Qed.

Lemma Isubseteq_antisym : forall x y, Isubseteq x y -> Isubseteq y x -> x == y.
Proof.
  unfold Isubseteq, Ieq.
  intros x y H H0. destruct H, H0.
  split. q_order. q_order.
Qed.

Lemma Isubseteq_trans : forall x y z, Isubseteq x y -> Isubseteq y z -> Isubseteq x z.
Proof.
  unfold Isubseteq. intros x y z H H0.
  destruct H as (H, H1), H0 as (H0, H2).
  split. q_order. q_order.
Qed.

Lemma Isubseteq_intersection : forall x y,
  Isubseteq (Iintersection x y) x /\ Isubseteq (Iintersection x y) y.
Proof.
  unfold Iintersection, Isubseteq. intros. simpl.
  rewrite Q.max_le_iff, Q.max_le_iff, Q.min_le_iff, Q.min_le_iff.
  split.
  - split. left. q_order. left. q_order.
  - split. right. q_order. right. q_order.
Qed.

Lemma Isubset_irrefl : forall x, Inempty x -> ~Isubset x x.
Proof.
  unfold Isubset, Inempty, not.
  intros x H H0. destruct H0.
  q_order.
Qed.

Lemma Isubset_trans : forall i j k, Isubset i j -> Isubset j k -> Isubset i k.
Proof.
  unfold Isubset. intros i j k H H0. destruct H, H0.
  split. q_order. q_order.
Qed.

Lemma Isubset_intersection_l : forall i j, Isubset i j -> Iintersection i j == i.
Proof.
  unfold Isubset, Iintersection, Ieq.
  destruct i, j. simpl.
  rewrite Q.max_l_iff, Q.min_l_iff.
  intro H. destruct H.
  split. q_order. q_order.
Qed.

Lemma Isupset_intersection_r : forall i j, Isupset i j -> Iintersection i j == j.
Proof.
  unfold Isupset, Iintersection, Ieq.
  destruct i, j. simpl.
  rewrite Q.min_r_iff, Q.max_r_iff.
  intro H. destruct H.
  split. q_order. q_order.
Qed.

Definition Idot (i : Interval) := (lower i == upper i)%Q.

Lemma Iintersection_if_divided1 : forall x y, x < y -> Iempty (Iintersection x y).
Proof.
  unfold Ilt, Iempty, Iintersection.
  destruct x, y.
  simpl.
  rewrite Qmin_lt_max_iff.
  intros. now left; right.
Qed.

Lemma Iintersection_if_divided2 : forall x y,
  Inempty x -> Inempty y -> (upper x == lower y)%Q -> Idot (Iintersection x y).
Proof.
  unfold Inempty, Idot, Iintersection.
  simpl. intros.
  rewrite <- Q.max_l_iff in H. rewrite <- Q.min_l_iff in H0.
  rewrite <- H1, Q.max_comm, H, H1, H0. q_order.
Qed.

Lemma Iintersection_if_divided3 : forall x y,
  (lower y < upper x)%Q /\ (lower x <= lower y)%Q /\ (upper x <= upper y)%Q ->
    Inempty (Iintersection x y).
Proof.
  unfold Inempty, Iintersection.
  simpl. intros x y H. destruct H as (H, H0), H0.
  rewrite Q.max_lub_iff, Q.min_glb_iff, Q.min_glb_iff.
  split.
  - split. q_order. q_order.
  - split. q_order. q_order.
Qed.

Lemma Iintersection_if_divided4 : forall x y,
  x == y -> x == Iintersection x y /\ y == Iintersection x y.
Proof.
  unfold Ieq, Iintersection.
  simpl. intros x y H.  destruct H.
  rewrite Qeq_sym_iff, Q.max_l_iff
        , Qeq_sym_iff, Q.min_l_iff
        , Qeq_sym_iff, Q.max_r_iff
        , Qeq_sym_iff, Q.min_r_iff.
  split.
  - split. q_order. q_order.
  - split. q_order. q_order.
Qed.

Lemma Iintersection_if_divided5 : forall x y, Isubset x y -> Iintersection x y == x.
Proof.
  unfold Isubset, Iintersection, Ieq.
  simpl. intros x y H. destruct H.
  rewrite Q.max_l_iff, Q.min_l_iff.
  split. q_order. q_order.
Qed.

Lemma Iintersection_if_divided6 : forall x y, Isubset y x -> Iintersection y x == y.
Proof.
  now intros; apply Iintersection_if_divided5.
Qed.

Lemma Iintersection_if_divided7 : forall x y,
  (lower x < upper y)%Q /\ (lower y <= lower x)%Q /\ (upper y <= upper x)%Q ->
    Inempty (Iintersection y x).
Proof.
  now intros; apply Iintersection_if_divided3.
Qed.

Lemma Iintersection_if_divided8 : forall x y,
  Inempty y -> Inempty x ->
  (upper y == lower x)%Q -> Idot (Iintersection y x).
Proof.
  now intros; apply Iintersection_if_divided2.
Qed.

Lemma Iintersection_if_divided9 : forall x y, y < x -> Iempty (Iintersection y x).
Proof.
  now intros; apply Iintersection_if_divided1.
Qed.

Lemma Iempty_intersection : forall i j, Iempty i -> Iempty (Iintersection i j).
Proof.
  unfold Iempty, Iintersection.
  simpl. intros.
  rewrite Qmin_lt_max_iff.
  now left; left.
Qed.

Definition Ioverlap (i j : Interval) : Prop :=
  Inempty (Iintersection i j).

Lemma Ioverlap_comm : forall i j, Ioverlap i j <-> Ioverlap j i.
Proof.
  unfold Ioverlap, Inempty, Iintersection.
  intros. simpl. split.
  - now rewrite Qmax_lel_comm, Qmin_ler_comm.
  - now rewrite Qmax_lel_comm, Qmin_ler_comm.
Qed.

Lemma Ilt_not_overlap : forall i j,
  i < j -> ~Ioverlap i j.
Proof.
  unfold Ilt, Ioverlap, Inempty, Iintersection.
  destruct i, j. simpl.
  rewrite Q.max_lub_iff, Q.min_glb_iff, Q.min_glb_iff.
  intros H H0. destruct H0 as (H0, H1), H0, H1.
  q_order.
Qed.

Lemma Igt_not_overlap : forall i j,
  i > j -> ~Ioverlap i j.
Proof.
  intros. rewrite Ioverlap_comm. now apply Ilt_not_overlap.
Qed.

Lemma Ioverlap_not_lt : forall i j, Ioverlap i j -> ~i < j.
Proof.
  unfold Ioverlap, Inempty, Iintersection, Ilt.
  destruct i, j. simpl.
  rewrite Qmax_le_min_iff.
  intros H H0. destruct H as (H, H1), H, H1.
  q_order.
Qed.

Lemma Ioverlap_not_gt : forall i j, Ioverlap i j -> ~i > j.
Proof.
  intros i j.
  rewrite Ioverlap_comm.
  now apply Ioverlap_not_lt.
Qed.

Lemma not_lt_gt_overlap : forall i j, Inempty i -> Inempty j -> ~i < j /\ ~i > j -> Ioverlap i j.
Proof.
  unfold Ilt, Ioverlap,Inempty, Iintersection.
  destruct i, j. simpl.
  rewrite Qmax_le_min_iff.
  intros H H0 H1. destruct H1.
  split.
  - split. q_order. q_order.
  - split. q_order. q_order.
Qed.

Lemma Ioverlap_nempty_intersection_iff : forall i j,
  Inempty i -> Inempty j -> Inempty (Iintersection i j) <-> Ioverlap i j.
Proof.
  unfold Ioverlap, Inempty, Iintersection.
  destruct i, j. simpl.
  now rewrite Qmax_le_min_iff; intros.
Qed.

Lemma Iempty_intersection_not_overlap : forall i j,
  Inempty i -> Inempty j -> Iempty (Iintersection i j) -> ~Ioverlap i j.
Proof.
  unfold Iempty, Ioverlap, Inempty, Iintersection.
  destruct i, j. simpl.
  rewrite Qmin_lt_max_iff, Qmax_le_min_iff.
  intros H H0 H1 H2. destruct H2, H2, H3. destruct H1 as [H1|H1].
  -- destruct H1 as [H1|H1]. q_order. q_order.
  -- destruct H1 as [H1|H1]. q_order. q_order.
Qed.

Lemma Isubset_overlap :
  forall i j, Inempty i -> Inempty j -> Isubset i j -> Ioverlap i j.
Proof.
  unfold Isubset, Ioverlap, Inempty, Iintersection.
  destruct i, j. simpl.
  rewrite Qmax_le_min_iff.
  intros H H0 H1. destruct H1.
  split.
  - split. q_order. q_order.
  - split. q_order. q_order.
Qed.

Lemma Isupset_overlap :
  forall i j, Inempty i -> Inempty j -> Isupset i j -> Ioverlap i j.
Proof.
  intros. rewrite Ioverlap_comm. now apply Isubset_overlap.
Qed.

Lemma Ilt_overlap_gt_dec : forall x y, Inempty x -> Inempty y -> {x < y} + {Ioverlap x y} + {x > y}.
Proof.
  unfold Ilt, Ioverlap, Inempty, Iintersection.
  destruct x as (xl, xu), y as (yl, yu). simpl. intros.
  destruct (Qlt_le_dec xu yl).
  - now left; left.
  - destruct (Qlt_le_dec yu xl).
  -- right. q_order.
  -- left. right.
     rewrite Qmax_le_min_iff.
     split.
  --- split. q_order. q_order.
  --- split. q_order. q_order.
Qed.
