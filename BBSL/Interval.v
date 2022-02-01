Require Import Arith.

(** * Definition of [Interval] **)

Definition Interval : Type := { lb_ub | fst lb_ub <= snd lb_ub }.

Declare Scope Interval_scope.
Open Scope Interval_scope.

Definition lb (i : Interval) := match i with exist _ tuple _ => fst tuple end.
Definition ub (i : Interval) := match i with exist _ tuple _ => snd tuple end.
Definition width (i : Interval) := ub i - lb i.

(** Basic relations of Interval. **)

Definition Ieq i j := lb i = lb j /\ ub i = ub j.
Definition Ilt i j := ub i < lb j.
Definition Ile i j := ub i <= lb j.
Notation Igt a b := (Ilt b a) (only parsing).
Notation Ige a b := (Ile b a) (only parsing).

Definition Isubset i j := lb j < lb i /\ ub i <= ub j \/ lb j <= lb i /\ ub i < ub j.
Definition Isubseteq i j := lb j <= lb i /\ ub i <= ub j.
Notation Isupset a b := (Isubset b a) (only parsing).
Notation Isupseteq a b := (Isubseteq b a) (only parsing).

Definition Ioverlap (i j : Interval) : Prop :=
  (lb j <= ub i)%nat /\ (lb i <= ub j)%nat.

Definition Iintersection (i j : Interval) : Ioverlap i j -> Interval.
  unfold Ioverlap.
  destruct i as ((lbi, ubi), p), j as ((lbj, ubj), q). simpl in p, q. simpl.
  intros (Hlbj_le_ubi, Hlbi_le_ubj).
  assert (max lbi lbj <= min ubi ubj)%nat.
  rewrite Nat.max_lub_iff, Nat.min_glb_iff, Nat.min_glb_iff.
  repeat split. assumption. assumption. assumption. assumption.
  exact (exist _ (max lbi lbj, min ubi ubj) H).
Defined.

Infix "==" := Ieq (at level 70, no associativity) : Interval_scope.
Infix "<" := Ilt : Interval_scope.
Infix "<=" := Ile : Interval_scope.
Notation "x > y" := (Ilt y x)(only parsing) : Interval_scope.
Notation "x >= y" := (Ile y x)(only parsing) : Interval_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Interval_scope.

#[global]
Hint Unfold Ieq Ilt Ile Isubset Isubseteq Ioverlap Iintersection : iarith.
#[global]
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.


(** * Decidability *)

Theorem Ilt_overlap_gt_dec : forall i j, {i < j} + {Ioverlap i j} + {i > j}.
Proof.
  unfold Ilt, Ioverlap.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ubi lbj). destruct s.
  - now left; left.
  - left. right. split.
    apply Nat.lt_eq_cases. now right.
    rewrite e in p.
    apply (le_trans lbi lbj ubj p q).
  - destruct (lt_eq_lt_dec ubj lbi). destruct s.
  -- now right.
  -- left. right. split.
     apply Nat.lt_eq_cases. now left.
     apply Nat.lt_eq_cases. now right.
  -- left. right. split.
     apply Nat.lt_eq_cases. now left.
     apply Nat.lt_eq_cases. now left.
Qed.

(** Decidability of Ioverlap *)

(** disconnected *)
Notation dcleft i j := (Ilt i j) (only parsing).
Notation dcright i j := (dcleft j i) (only parsing).
Notation dc i j := (dcleft i j \/ dcright i j) (only parsing).

(** externally connected *)
Definition ecleft i j := ub i = lb j.
Notation ecright i j := (ecleft j i) (only parsing).
Notation ec i j := (ecleft i j \/ ecright i j) (only parsing).

(** equal *)
Notation eq i j := (Ieq i j) (only parsing).

(** partially overlapping *)
Definition poleft i j := (lb i < lb j)%nat /\ (lb j < ub i)%nat /\ (ub i < ub j)%nat.
Notation poright i j := (poleft j i) (only parsing).
Notation po i j := (poleft i j \/ poright i j) (only parsing).

(** tangential proper part *)
Definition tppleft i j := (lb i = lb j)%nat /\ (ub i < ub j)%nat.
Definition tppright i j := (lb j < lb i)%nat /\ (ub i = ub j)%nat.
Notation tpp i j := (tppleft i j \/ tppright i j) (only parsing).

(** tangential proper part inverse *)
Notation tppileft i j := (tppleft j i) (only parsing).
Notation tppiright i j := (tppright j i) (only parsing).
Notation tppi i j := (tpp j i) (only parsing).

(** non-tangential proper part *)
Definition ntpp i j := (lb j < lb i)%nat /\ (ub i < ub j)%nat.

(** non-tangential proper part inverse *)
Notation ntppi i j := (ntpp j i) (only parsing).

(** overlapping *)
Definition overlap i j :=
  ec i j \/ eq i j \/ po i j \/ tpp i j \/ tppi i j \/ ntpp i j \/ ntppi i j.

Theorem Ioverlap_dec : forall i j, Ioverlap i j ->
  { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { eq i j } + { ntppi i j } +
  { tppileft i j } + { ntpp i j } + { tppright i j } +
  { poright i j } + { ecright i j }.
Proof.
  unfold Ioverlap, ecleft, poleft, tppiright, tppleft, eq,
         ntppi, tppileft, ntpp, tppright, poright, ecright.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros (H, H0). destruct (lt_eq_lt_dec ubi lbj). destruct s.
  (* dcleft (ubi < lbj) *)
  - apply (le_lt_trans lbj ubi lbj H) in l. apply lt_irrefl in l. contradiction.
  (* ecleft (ubi = lbj) *)
  - now left; left; left; left; left; left; left; left; left; left.
  - destruct (lt_eq_lt_dec lbi lbj), (lt_eq_lt_dec ubi ubj). destruct s, s0.
  (* poleft (lbi < lbj /\ lbj < ubi /\ ubi < ubj) *)
  -- left; left; left; left; left; left; left; left; left. right.
     repeat split. assumption. assumption. assumption.
  (* tppiright (lbi < lbj /\ ubi = lbj) *)
  -- left; left; left; left; left; left; left; left; right.
     split. assumption. now apply eq_sym.
  (* tppleft (lbi = lbj /\ ubi < ubj) *)
  -- left; left; left; left; left; left; left; right.
     split. assumption. assumption.
  (* eq (lbi = lbj /\ ubi = ubj) *)
  -- left; left; left; left; left; left; right.
     split. assumption. assumption.
  -- destruct s.
  (* ntppi (lbi < lbj /\ ubj < ubi) *)
  --- left; left; left; left; left; right.
      split. assumption. assumption.
  (* tppileft (lbj = lbi /\ ubj < ubi) *)
  --- left; left; left; left; right.
      split. now apply eq_sym. assumption.
  -- destruct s.
  (* ntpp (lbj < lbi /\ ubi < ubj) *)
  --- left; left; left; right.
      split. assumption. assumption.
  (* tppright (lbj < lbi /\ ubi = ubj) *)
  --- left; left; right.
      split. assumption. assumption.
  -- destruct (lt_eq_lt_dec lbi ubj). destruct s.
  (* poright (lbj < lbi < ubj < ubi) *)
  --- left; right.
      repeat split. assumption. assumption. assumption.
  (* ecright (lbj = ubi) *)
  --- right. now apply eq_sym.
  (* dcright (lbi < ubj) *)
  --- apply (le_lt_trans lbi ubj lbi H0) in l2. apply lt_irrefl in l2. contradiction.
Qed.

(** * Decidability of Relation Connection Calculus *)

Theorem rcc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { eq i j } + { ntppi i j } +
  { tppileft i j } + { ntpp i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
Proof.
  intros i j. destruct (Ilt_overlap_gt_dec i j). destruct s.
  - now left; left; left; left; left; left; left; left; left; left; left; left.
  - destruct (Ioverlap_dec i j i0). repeat destruct s.
  -- now left; left; left; left; left; left; left; left; left; left; left; right.
  -- now left; left; left; left; left; left; left; left; left; left; right.
  -- now left; left; left; left; left; left; left; left; left; right.
  -- now left; left; left; left; left; left; left; left; right.
  -- now left; left; left; left; left; left; left; right.
  -- now left; left; left; left; left; left; right.
  -- now left; left; left; left; left; right.
  -- now left; left; left; left; right.
  -- now left; left; left; right.
  -- now left; left; right.
  -- now left; right.
  - now right.
Qed.


(** * Properties of basic relations *)

Theorem Ieq_refl : forall i, i == i.
Proof.
  auto with iarith.
Qed.

Theorem Ieq_sym : forall i j, i == j -> j == i.
Proof.
  unfold eq. intros i j (H, H0). split.
  apply (sym_equal H). apply (sym_equal H0).
Qed.

Lemma Ieq_sym_iff : forall i j, i == j <-> j == i.
Proof.
  split. apply Ieq_sym. apply Ieq_sym.
Qed.

Theorem Ieq_trans : forall i j k, i == j -> j == k -> i == k.
Proof.
  unfold eq. intros i j k (H, H0) (H1, H2). split.
  apply (eq_trans H H1). apply (eq_trans H0 H2).
Qed.

Theorem Ieq_dec : forall i j, {i == j} + {~ i == j}.
Proof.
  unfold Ieq. destruct i as ((lbi, ubi), p), j as ((lbj, ubj), q). simpl in p, q. simpl.
  destruct (Nat.eq_dec lbi lbj), (Nat.eq_dec ubi ubj).
  - left. split. assumption. assumption.
  - right. intros (H, H0). apply (n H0).
  - right. intros (H, H0). apply (n H).
  - right. intros (H, H0). apply (n H).
Qed.

Theorem Inot_eq_sym i j : ~ i == j -> ~ j == i.
Proof.
  unfold Ieq, not. destruct i as ((lbi, ubi), p), j as ((lbj, ubj), q). simpl in p, q. simpl.
  intros H (H0, H1). apply H. split. now apply eq_sym in H0. now apply eq_sym in H1.
Qed.

Theorem Ilt_irrefl : forall i, ~i < i.
Proof.
  auto with iarith.
  unfold Ilt. intros (i, p). simpl. now apply le_not_lt.
Qed.

Theorem Ilt_asym : forall i j, i < j -> ~j < i.
Proof.
  unfold Ilt. intros (i, p) (j, q). simpl. Nat.order.
Qed.

Theorem Ilt_trans : forall i j k, i < j -> j < k -> i < k.
Proof.
  unfold Ilt. intros (i, p) (j, q) (k, r). simpl. Nat.order.
Qed.

Lemma Ilt_eq : forall i j k, i < j -> j == k -> i < k.
Proof.
  unfold Ilt, eq. intros (i, p) (j, q) (k, r). simpl. intros H (H0, H1). Nat.order.
Qed.

Lemma eq_Ilt : forall i j k, i == j -> j < k -> i < k.
Proof.
  unfold Ilt, eq. intros (i, p) (j, q) (k, r). simpl. intros (H, H0). Nat.order.
Qed.

Lemma Ile_antisym : forall i j, i <= j -> j <= i -> i == j.
Proof.
  unfold Ile, Ieq. intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros Hubi_le_lbj Hubj_le_lbi. split.
  - apply (le_trans lbi ubi lbj p) in Hubi_le_lbj as Hlbi_le_lbj.
    apply (le_trans lbj ubj lbi q) in Hubj_le_lbi as Hlbj_le_lbi.
    apply (le_antisym lbi lbj Hlbi_le_lbj Hlbj_le_lbi).
  - apply (le_trans ubi lbj ubj Hubi_le_lbj) in q as Hubi_le_ubj.
    apply (le_trans ubj lbi ubi Hubj_le_lbi) in p as Hubj_le_ubi.
    apply (le_antisym ubi ubj Hubi_le_ubj Hubj_le_ubi).
Qed.

Lemma Ile_trans : forall i j k, i <= j -> j <= k -> i <= k.
Proof.
  unfold Ile. intros ((lbi, ubi), p) ((lbj, ubj), q) ((lbk, ubk), r).
  simpl in p, q, r. simpl. intros Hubi_le_lbj Hubj_le_lbk.
  apply (le_trans ubi lbj ubj Hubi_le_lbj) in q as Hubi_le_ubj.
  apply (le_trans ubi ubj lbk Hubi_le_ubj Hubj_le_lbk).
Qed.

Lemma Isubset_irrefl : forall i, ~Isubset i i.
Proof.
  unfold Isubset. intros i [(Hlbi_lt_lbi, Hubi_le_ubi) | (Hlbi_le_lbi, Hubi_lt_ubi)].
  apply (lt_irrefl (lb i) Hlbi_lt_lbi).
  apply (lt_irrefl (ub i) Hubi_lt_ubi).
Qed.

Lemma Isubset_trans : forall i j k, Isubset i j -> Isubset j k -> Isubset i k.
Proof.
  unfold Isubset. intros i j k.
  intros [(Hlbj_lt_lbi, Hubi_le_ubj) | (Hlbj_le_lbi, Hubi_lt_ubj)]
         [(Hlbk_lt_lbj, Hubj_le_ubk) | (Hlbk_le_lbj, Hubj_lt_ubk)].
  - left. split.
    now apply (lt_trans (lb k) (lb j) (lb i)).
    now apply (le_trans (ub i) (ub j) (ub k)).
  - left. split.
    now apply (le_lt_trans (lb k) (lb j) (lb i)).
    apply Nat.lt_eq_cases. left. now apply (le_lt_trans (ub i) (ub j) (ub k)).
  - left. split.
    now apply (lt_le_trans (lb k) (lb j) (lb i)).
    apply Nat.lt_eq_cases. left. now apply (lt_le_trans (ub i) (ub j) (ub k)).
  - right. split.
    now apply (le_trans (lb k) (lb j) (lb i)).
    now apply (lt_trans (ub i) (ub j) (ub k)).
Qed.

Lemma Isubseteq_refl : forall i, Isubseteq i i.
Proof.
  unfold Isubseteq. split. apply le_refl. apply le_refl.
Qed.

Lemma Isubseteq_antisym : forall i j, Isubseteq i j -> Isubseteq j i -> i == j.
Proof.
  unfold Isubseteq, Ieq.
  intros i j (Hlbj_le_lbi, Hubi_le_ubj) (Hlbi_le_lbj, Hubj_le_ubi). split.
  apply (le_antisym (lb i) (lb j) Hlbi_le_lbj Hlbj_le_lbi).
  apply (le_antisym (ub i) (ub j) Hubi_le_ubj Hubj_le_ubi).
Qed.

Lemma Isubseteq_trans : forall i j k, Isubseteq i j -> Isubseteq j k -> Isubseteq i k.
Proof.
  unfold Isubseteq.
  intros i j k (Hlbj_le_lbi, Hubi_le_ubj) (Hlbk_le_lbj, Hubj_le_ubk). split.
  apply (le_trans (lb k) (lb j) (lb i) Hlbk_le_lbj Hlbj_le_lbi).
  apply (le_trans (ub i) (ub j) (ub k) Hubi_le_ubj Hubj_le_ubk).
Qed.

Lemma Isubset_eq_cases : forall i j, Isubseteq i j -> Isubset i j \/ Ieq i j.
Proof.
  unfold Isubseteq, Isubset, Ieq.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros (Hlbj_le_lbi, Hubi_le_ubj).
  destruct (lt_eq_lt_dec lbi lbj). destruct s.
  - apply (le_lt_trans lbj lbi lbj Hlbj_le_lbi) in l as Hlbj_lt_lbj.
    now apply lt_irrefl in Hlbj_lt_lbj.
  - destruct (lt_eq_lt_dec ubj ubi). destruct s.
  -- apply (le_lt_trans ubi ubj ubi Hubi_le_ubj) in l as Hubi_lt_ubi.
     now apply lt_irrefl in Hubi_lt_ubi.
  -- right. split. assumption. now apply sym_equal.
  -- left. right. split. assumption. assumption.
  - destruct (lt_eq_lt_dec ubj ubi). destruct s.
  -- apply (le_lt_trans ubi ubj ubi Hubi_le_ubj) in l0 as Hubi_lt_ubi.
     now apply lt_irrefl in Hubi_lt_ubi.
  -- left. left. split. assumption. assumption.
  -- left. right. split. assumption. assumption.
Qed.

Lemma Isubset_subseteq_trans : forall i j k,
  Isubset i j -> Isubseteq j k -> Isubset i k.
Proof.
  unfold Isubset, Isubseteq.
  intros ((lbi, ubi), p) ((lbj, ubj), q) ((lbk, ubk), r). simpl in p, q, r. simpl.
  intros [(Hlbj_lt_lbi, Hubi_le_ubj) | (Hlbj_le_lbi, Hubi_lt_ubj)] (Hlbk_le_lbj, Hubj_le_ubk).
  - left. split.
    now apply (le_lt_trans lbk lbj lbi).
    now apply (le_trans ubi ubj ubk).
  - right. split.
    now apply (le_trans lbk lbj lbi).
    now apply (lt_le_trans ubi ubj ubk).
Qed.

Lemma Isubseteq_subset_trans : forall i j k,
  Isubseteq i j -> Isubset j k -> Isubset i k.
Proof.
  unfold Isubseteq, Isubset.
  intros ((lbi, ubi), p) ((lbj, ubj), q) ((lbk, ubk), r). simpl in p, q, r. simpl.
  intros (Hlbj_le_lbi, Hubi_le_ubj) [(Hlbk_lt_lbj, Hubj_le_ubk) | (Hlbk_le_lbj, Hubj_lt_ubk)].
  - left. split.
    now apply (lt_le_trans lbk lbj lbi).
    now apply (le_trans ubi ubj ubk).
  - right. split.
    now apply (le_trans lbk lbj lbi).
    now apply (le_lt_trans ubi ubj ubk).
Qed.

Lemma Ioverlap_refl : forall i, Ioverlap i i.
Proof.
  unfold Ioverlap. intros ((lbi, ubi), p). simpl in p. simpl.
  split. assumption. assumption.
Qed.

Lemma Ioverlap_sym : forall i j, Ioverlap i j -> Ioverlap j i.
Proof.
  unfold Ioverlap. intros i j (Hlbj_le_ubi, Hlbi_le_lbj). split.
  assumption. assumption.
Qed.

Lemma Isubset_overlap :
  forall i j, Isubset i j -> Ioverlap i j.
Proof.
  unfold Isubset, Ioverlap.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros [(Hlbj_lt_lbi, Hubi_le_ubj) | (Hlbj_le_lbi, Hubi_lt_ubj)].
  - split.
    apply Nat.lt_eq_cases. left. now apply (lt_le_trans lbj lbi ubi).
    now apply (le_trans lbi ubi ubj).
  - split.
    now apply (le_trans lbj lbi ubi).
    apply Nat.lt_eq_cases. left. now apply (le_lt_trans lbi ubi ubj).
Qed.

Lemma Isupset_overlap :
  forall i j, Isupset i j -> Ioverlap i j.
Proof.
  intros. apply Ioverlap_sym. now apply Isubset_overlap.
Qed.

Lemma Iintersection_comm : forall i j (Hioj : Ioverlap i j) (Hjoi : Ioverlap j i), Iintersection i j Hioj == Iintersection j i Hjoi.
Proof.
  unfold Iintersection, Ieq, Ioverlap.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros (Hlbj_le_ubi, Hlbi_le_ubj) (H, H0).
  simpl. split.
  apply Nat.max_comm. apply Nat.min_comm.
Qed.

Lemma Isubseteq_intersection : forall i j (Hioj : Ioverlap i j),
  Isubseteq (Iintersection i j Hioj) i /\ Isubseteq (Iintersection i j Hioj) j.
Proof.
  unfold Iintersection, Ieq, Ioverlap, Isubseteq.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros (Hlbj_le_ubi, Hlbi_le_ubj). simpl. repeat split.
  - rewrite Nat.max_le_iff. left. apply le_refl.
  - rewrite Nat.min_le_iff. left. apply le_refl.
  - rewrite Nat.max_le_iff. right. apply le_refl.
  - rewrite Nat.min_le_iff. right. apply le_refl.
Qed.

Lemma Isubset_intersection_l : forall i j (Hioj : Ioverlap i j),
  Isubset i j -> Iintersection i j Hioj == i.
Proof.
  unfold Isubset, Iintersection, Ieq.
  intros ((lbi, ubi), p) ((lbj, ubj), q). simpl in p, q. simpl.
  intros (Hlbj_le_ubi, Hlbi_le_ubj) Hisubj. simpl in Hlbj_le_ubi, Hlbi_le_ubj. simpl.
  rewrite Nat.max_l_iff, Nat.min_l_iff.
  destruct Hisubj as [(Hlbj_lt_lbi, Hubi_le_ubj) | (lbj_le_lbi, ubi_lt_ubj)].
  - split. now apply lt_le_weak. assumption.
  - split. assumption. now apply lt_le_weak.
Qed.

Lemma Isupset_intersection_r : forall i j (Hioj : Ioverlap i j),
  Isupset i j -> Iintersection i j Hioj == j.
Proof.
  intros.
  apply Ioverlap_sym in Hioj as Hjoi.
  assert (Iintersection i j Hioj == Iintersection j i Hjoi) as Hiij_eq_jii.
  apply (Iintersection_comm i j Hioj Hjoi).
  apply (Ieq_trans (Iintersection i j Hioj) (Iintersection j i Hjoi) j Hiij_eq_jii).
  now apply Isubset_intersection_l.
Qed.


(*
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
*)

(*
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
*)

