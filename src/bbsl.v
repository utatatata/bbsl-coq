Require Import ClassicalDescription QArith QOrderedType Qminmax GenericMinMax String Bool List FMapList OrderedTypeEx Ensembles Bool Ltac2.Option.
Import ListNotations.

Declare Scope BBSL_scope.

Local Open Scope bool_scope.
Local Open Scope Q_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope BBSL_scope.

Definition Interval : Type := Q * Q.

Definition lower (i : Interval) : Q :=
  match i with
  | (l, _) => l
  end.

Definition upper (i : Interval) : Q :=
  match i with
  | (_, u) => u
  end.

Definition IisEmpty (i : Interval) : Prop :=
  lower i > upper i.

Definition IisNotEmpty (i : Interval) : Prop :=
  lower i <= upper i.

Definition Iin (v : Q) (i : Interval) : Prop :=
  (lower i <= v /\ v <= upper i)%Q.

Lemma Iin_lower : forall i, ~IisEmpty i -> Iin (lower i) i.
Proof.
  intros. unfold Iin. unfold IisEmpty in H.
  split. q_order. q_order.
Qed.

Lemma Iin_upper : forall i, ~IisEmpty i -> Iin (upper i) i.
Proof.
  intros. unfold Iin. unfold IisEmpty in H.
  split. q_order. q_order.
Qed.

Definition width (i : Interval) : Q :=
  Qmax 0 (upper i - lower i).

Definition Ieq (i0 i1 : Interval) := lower i0 == lower i1 /\ upper i0 == upper i1.
Definition Ilt (i0 i1 : Interval) := upper i0 < lower i1.
Definition Ile (i0 i1 : Interval) := upper i0 <= lower i1.
Notation Igt a b := (Ilt b a) (only parsing).
Notation Ige a b := (Ile b a) (only parsing).

Infix "==" := Ieq (at level 70, no associativity) : BBSL_scope.
Infix "<" := Ilt : BBSL_scope.
Infix "<=" := Ile : BBSL_scope.
Notation "x > y" := (Ilt y x)(only parsing) : BBSL_scope.
Notation "x >= y" := (Ile y x)(only parsing) : BBSL_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : BBSL_scope.

Lemma Ieq_refl : forall x, x == x.
Proof.
  unfold Ieq. intros.
  split. apply Qeq_refl. apply Qeq_refl.
Qed.

Lemma Ilt_gt_dual : forall i0 i1, Ilt i0 i1 <-> Igt i1 i0.
Proof.
  intros.
  unfold Ilt. unfold Igt. unfold iff.
  split. trivial. trivial.
Qed.

Lemma Ieq_sym : forall x y, x == y -> y == x.
Proof.
  unfold Ieq. intros. destruct H. split.
  apply (Qeq_sym (lower x) (lower y) H).
  apply (Qeq_sym (upper x) (upper y) H0).
Qed.

Lemma Ieq_sym_iff : forall x y, x == y <-> y == x.
Proof.
  intros. split.
  apply Ieq_sym. apply Ieq_sym.
Qed.

Lemma Ieq_trans : forall x y z, x == y /\ y == z -> x == z.
Proof.
  unfold Ieq. intros. destruct H. destruct H, H0. split.
  apply (Qeq_trans (lower x) (lower y) (lower z) H H0).
  apply (Qeq_trans (upper x) (upper y) (upper z) H1 H2).
Qed.


Lemma Ilt_antisymm : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Ilt i0 i1 -> ~Ilt i1 i0.
Proof.
  unfold Ilt. intros.
  unfold IisEmpty in H. destruct H.
  q_order.
Qed.

Lemma Igt_antisymm : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Igt i0 i1 -> ~Igt i1 i0.
Proof.
  intros i0 i1.
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Ilt_antisymm i1 i0).
Qed.

Lemma Ilt_not_gt : forall i0 i1,
  ~IisEmpty i0 /\ ~IisEmpty i1 -> Ilt i0 i1 -> ~Igt i0 i1.
Proof.
  intros i0 i1.
  apply (Ilt_antisymm i0 i1).
Qed.

Lemma Igt_not_lt : forall i0 i1,
  ~IisEmpty i0 /\ ~IisEmpty i1 -> Igt i0 i1 -> ~Ilt i0 i1.
Proof.
  intros i0 i1.
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Ilt_not_gt i1 i0).
Qed.

Definition Iintersection (i0 i1 : Interval) : Interval :=
  (Qmax (lower i0) (lower i1), Qmin (upper i0) (upper i1)).

Goal forall q q0 q1 : Q, ((Qmax q0 q1, q) == (Qmax q1 q0, q)).
Proof.
  intros. unfold Ieq. simpl.
  rewrite (Q.max_comm q1 q0).
  split.
  apply Qeq_refl.
  apply Qeq_refl.
Qed.

Lemma Iintersection_comm : forall i0 i1, Iintersection i0 i1 == Iintersection i1 i0.
Proof.
  unfold Iintersection.
  intros.
  destruct i0. destruct i1.
  simpl. unfold Ieq. simpl.
  rewrite (Q.max_comm q1 q).
  rewrite (Q.min_comm q2 q0).
  split. apply Qeq_refl. apply Qeq_refl.
Qed.

Lemma Iempty_intersection : forall i0 i1, IisEmpty i0 -> IisEmpty (Iintersection i0 i1).
Proof.
  unfold IisEmpty. unfold Iintersection. simpl.
  intros. destruct i0. destruct i1. simpl. simpl in H.
  rewrite (Q.min_lt_iff q0 q2 (Qmax q q1)).
  rewrite (Q.max_lt_iff q q1 q0).
  left. left. assumption.
Qed.

Definition Isubset (i0 i1 : Interval) : Prop :=
  (lower i1 < lower i0)%Q /\ (upper i0 < upper i1)%Q.

Definition Isupset (i0 i1 : Interval) : Prop :=
  (lower i0 < lower i1)%Q /\ (upper i1 < upper i0)%Q.

Lemma Isubset_supset_dual : forall i0 i1, Isubset i0 i1 <-> Isupset i1 i0.
Proof.
  intros.
  unfold Isubset. unfold Isupset. unfold iff.
  split. trivial. trivial.
Qed.

Lemma Isubset_trans : forall i0 i1 i2, Isubset i0 i1 /\ Isubset i1 i2 -> Isubset i0 i2.
Proof.
  unfold Isubset.
  intros.
  simpl. simpl in H. destruct H. destruct H. destruct H0.
  split.
  - apply (Qlt_trans (lower i2) (lower i1) (lower i0) H0 H).
  - apply (Qlt_trans (upper i0) (upper i1) (upper i2) H1 H2). 
Qed.

Definition Isubseteq (i0 i1 : Interval) : Prop :=
  Isubset i0 i1 \/ i0 == i1.

Definition Isupseteq (i0 i1 : Interval) : Prop :=
  Isupset i0 i1 \/ i0 == i1.

Lemma Isubset_intersection_l : forall i0 i1, Isubset i0 i1 -> Iintersection i0 i1 == i0.
Proof.
  unfold Isubset. unfold Iintersection.
  destruct i0. destruct i1. simpl.
  intros. destruct H.
  unfold Ieq. simpl. split.
  - rewrite (Q.max_l q q1 (Qlt_le_weak q1 q H)). apply Qeq_refl.
  - rewrite (Q.min_l q0 q2 (Qlt_le_weak q0 q2 H0)). apply Qeq_refl.
Qed.

Lemma Isupset_intersection_r : forall i0 i1, Isupset i0 i1 -> Iintersection i0 i1 == i1.
Proof.
  unfold Isupset. unfold Iintersection.
  destruct i0. destruct i1. simpl.
  intros. destruct H.
  unfold Ieq. simpl. split.
  - rewrite (Q.max_r q q1 (Qlt_le_weak q q1 H)). apply Qeq_refl.
  - rewrite (Q.min_r q0 q2 (Qlt_le_weak q2 q0 H0)). apply Qeq_refl.
Qed.

Definition Ioverlap (i0 i1 : Interval) : Prop :=
  ~IisEmpty (Iintersection i0 i1).

(* helper *)
Lemma Qmin_ltl_comm : forall q q0 q1 : Q, (Qmin q0 q1 < q)%Q <-> (Qmin q1 q0 < q)%Q.
Proof.
  intros.
  rewrite (Q.min_comm q1 q0).
  split.
  - intros. assumption.
  - intros. assumption.
Qed.

(* helper *)
Lemma Qmax_ltr_comm : forall q q0 q1 : Q, (q < Qmax q0 q1)%Q <-> (q < Qmax q1 q0)%Q.
Proof.
  intros.
  rewrite (Q.max_comm q1 q0).
  split.
  - intros. assumption.
  - intros. assumption.
Qed.

Lemma Ioverlap_comm : forall i0 i1, Ioverlap i0 i1 <-> Ioverlap i1 i0.
Proof.
  unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold not. simpl.
  intros. destruct i0. destruct i1. simpl. split.
  - intros.
    rewrite (Qmin_ltl_comm (Qmax q1 q) q2 q0) in H0.
    rewrite (Qmax_ltr_comm (Qmin q0 q2) q1 q) in H0.
    apply H.
    assumption.
  - intros.
    rewrite (Qmin_ltl_comm (Qmax q q1) q0 q2) in H0.
    rewrite (Qmax_ltr_comm (Qmin q2 q0) q q1) in H0.
    apply H.
    assumption.
Qed.

Lemma Ilt_not_overlap : forall i0 i1,
  Ilt i0 i1 -> ~Ioverlap i0 i1.
Proof.
  unfold Ilt. unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold not.
  intros. destruct i0. destruct i1. simpl in H0. simpl in H.
  destruct H0.
  rewrite (Q.max_lt_iff q q1 (Qmin q0 q2)).
  rewrite (Q.min_lt_iff q0 q2 q1).
  right. left.
  assumption.
Qed.

Lemma Igt_not_overlap : forall i0 i1,
  Igt i0 i1 -> ~Ioverlap i0 i1.
Proof.
  intros i0 i1.
  rewrite (Ioverlap_comm i0 i1).
  apply (Ilt_not_overlap i1 i0).
Qed.

Lemma Ioverlap_not_lt : forall i0 i1, Ioverlap i0 i1 -> ~Ilt i0 i1.
Proof.
  unfold Ilt. unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold not.
  intros. destruct i0. destruct i1. simpl in H. simpl in H0.
  destruct H.
  rewrite (Q.min_lt_iff q0 q2 (Qmax q q1)).
  rewrite (Q.max_lt_iff q q1 q0).
  left. right.
  assumption.
Qed.

Lemma Ioverlap_not_gt : forall i0 i1, Ioverlap i0 i1 -> ~Igt i0 i1.
Proof.
  intros i0 i1.
  rewrite (Ioverlap_comm i0 i1).
  apply (Ioverlap_not_lt i1 i0).
Qed.

(* helper *)
Lemma DNE : forall A, ~~A <-> A.
Proof.
  intros.
  destruct (excluded_middle_informative A).
  split. 
  - intros. assumption.
  - intros.
    unfold not. intros.
    apply (H0 H).
  - unfold not. split. 
    intros. contradiction. intros. apply (H0 H).
Qed.

(* use classical facts *)
Lemma not_Ioverpal_lt_gt : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> ~Ioverlap i0 i1 <-> Ilt i0 i1 \/ Igt i0 i1.
Proof.
  unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold Ilt. unfold Igt.
  intros. destruct i0. destruct i1. simpl.
  rewrite (DNE (Qmin q0 q2 < Qmax q q1)%Q).
  simpl in H. unfold not in H.  destruct H.
  rewrite (Q.min_lt_iff q0 q2 (Qmax q q1)).
  rewrite (Q.max_lt_iff q q1 q0).
  rewrite (Q.max_lt_iff q q1 q2).
  split.
  - intros.
    destruct H1. destruct H1.
    contradiction.
    left. assumption.
    destruct H1.
    right. assumption.
    contradiction.
  - intros.
    destruct H1.
    left. right. assumption.
    right. left. assumption.
Qed.

Lemma not_lt_gt_overlap : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> ~Ilt i0 i1 /\ ~Igt i0 i1 -> Ioverlap i0 i1.
Proof.
  unfold Ilt. unfold Igt. unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold not. simpl.
  intros.
  destruct i0. destruct i1. simpl in H.  simpl in H0. simpl in H1.
  destruct H. destruct H0.
  rewrite (Q.min_lt_iff q0 q2 (Qmax q q1)) in H1.
  rewrite (Q.max_lt_iff q q1 q0) in H1.
  rewrite (Q.max_lt_iff q q1 q2) in H1.
  destruct H1. destruct H1.
  contradiction.
  contradiction.
  destruct H1. contradiction. contradiction.
Qed.

Lemma Qlt_asym : forall q0 q1 : Q, ~((q0 < q1)%Q /\ (q1 < q0)%Q).
Proof.
  unfold not. intros. destruct H.
  q_order.
Qed.

Lemma Ilt_overlap_gt : forall i0 i1,
  IisNotEmpty i0 /\ IisNotEmpty i1 ->
    Ilt i0 i1 \/Ioverlap i0 i1 \/ Igt i0 i1.
Proof.
  unfold Ioverlap. unfold Ilt. unfold Igt. unfold IisEmpty. unfold IisNotEmpty. unfold Iintersection. unfold not. simpl.
  destruct i0 as (i0l, i0u). destruct i1 as (i1l, i1u). simpl.
  rewrite (Q.min_lt_iff i0u i1u (Qmax i0l i1l)).
  rewrite (Q.max_lt_iff i0l i1l i0u).
  rewrite (Q.max_lt_iff i0l i1l i1u).
  intros. destruct H.
  destruct (Qlt_le_dec i0u i1l).
  - left. assumption.
  - destruct (Qlt_le_dec i1u i0l).
  -- right. right. assumption.
  -- right. left. intros. destruct H1. destruct H1.
  --- apply (Qle_lteq i0l i0u) in H. destruct H.
  ---- apply (Qlt_asym i0l i0u (conj H H1)). 
  ---- rewrite H in H1. apply (Qlt_irrefl i0u H1).
  --- apply (Qle_lteq i1l i0u) in q. destruct q.
  ---- apply (Qlt_asym i0u i1l (conj H1 H2)).
  ---- rewrite H2 in H1. apply (Qlt_irrefl i0u H1).
  --- destruct H1.
  ---- apply (Qle_lteq i0l i1u) in q0. destruct q0.
  ----- apply (Qlt_asym i0l i1u (conj H2 H1)).
  ----- rewrite H2 in H1. apply (Qlt_irrefl i1u H1).
  ---- apply (Qle_lteq i1l i1u) in H0. destruct H0.
  ----- apply (Qlt_asym i1l i1u (conj H0 H1)).
  ----- rewrite H0 in H1. apply (Qlt_irrefl i1u H1).
Qed. 

    
Lemma Isubset_overlap :
  forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Isubset i0 i1 -> Ioverlap i0 i1.
Proof.
  unfold Ioverlap. unfold Isubset. unfold Iintersection. unfold IisEmpty. unfold not. simpl.
  intros. destruct i0. destruct i1. simpl in H. simpl in H0. simpl in H1.
  destruct H. destruct H0.
  rewrite (Q.min_lt_iff q0 q2 (Qmax q q1)) in H1.
  rewrite (Q.max_lt_iff q q1 q0) in H1.
  rewrite (Q.max_lt_iff q q1 q2) in H1.
  destruct H1. destruct H1.
  contradiction.
  apply (H (Qlt_trans q0 q1 q H1 H0)). 
  destruct H1. apply (H (Qlt_trans q0 q2 q H3 H1)).
  contradiction.
Qed.

Lemma Isupset_overlap :
  forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Isupset i0 i1 -> Ioverlap i0 i1.
Proof.
  intros i0 i1.
  rewrite <- (Isubset_supset_dual i1 i0).
  rewrite (Ioverlap_comm i0 i1).
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Isubset_overlap i1 i0).
Qed.

Definition BB : Type := Interval * Interval.

Definition projx (bb : BB) : Interval :=
  match bb with
  | (x, _) => x
  end.

Definition projy (bb : BB) : Interval :=
  match bb with
  | (_, y) => y
  end.

Definition projxl (bb : BB) : Q :=
  lower (projx bb).

Definition projxu (bb : BB) : Q :=
  upper (projx bb).

Definition projyl (bb : BB) : Q :=
  lower (projy bb).

Definition projyu (bb : BB) : Q :=
  upper (projy bb).

Definition BBisEmpty (bb : BB) : Prop :=
  IisEmpty (projx bb) /\ IisEmpty (projy bb).

Definition BBisNotEmpty (bb : BB) : Prop :=
  IisNotEmpty (projx bb) /\ IisNotEmpty (projy bb).

Definition BBeq (bb0 bb1 : BB) : Prop :=
  Ieq (projx bb0) (projx bb1) /\ Ieq (projy bb0) (projy bb1).

Infix "==" := BBeq (at level 70, no associativity) : BBSL_scope.

Lemma BBeq_refl : forall x, x == x.
Proof.
  unfold BBeq. intros. split.
  apply Ieq_refl. apply Ieq_refl.
Qed.

Lemma BBeq_sym : forall x y, x == y -> y == x.
Proof.
  unfold BBeq. intros. destruct H. split.
  apply (Ieq_sym (projx x) (projx y) H).
  apply (Ieq_sym (projy x) (projy y) H0).
Qed.

Lemma BBeq_sym_iff : forall x y, x == y <-> y == x.
Proof.
  intros. split.
  apply BBeq_sym. apply BBeq_sym.
Qed.

Lemma BBeq_trans : forall x y z, x == y /\ y == z -> x == z.
Proof.
  unfold BBeq. intros. destruct H. destruct H, H0. split.
  apply (Ieq_trans (projx x) (projx y) (projx z) (conj H H0)).
  apply (Ieq_trans (projy x) (projy y) (projy z) (conj H1 H2)).
Qed.

Definition BBoverlap (bb0 bb1 : BB) : Prop :=
  Ioverlap (projx bb0) (projx bb1) /\ Ioverlap (projy bb0) (projy bb1).

Definition BBsubset (bb0 bb1 : BB) : Prop :=
  Isubset (projx bb0) (projx bb0) /\ Isubset (projy bb0) (projy bb0).

Definition BBsupset (bb0 bb1 : BB) : Prop :=
  Isupset (projx bb0) (projx bb0) /\ Isupset (projy bb0) (projy bb0).

Definition BBsubseteq (bb0 bb1 : BB) : Prop :=
  Isubseteq (projx bb0) (projx bb0) /\ Isubseteq (projy bb0) (projy bb0).

Definition BBsupseteq (bb0 bb1 : BB) : Prop :=
  Isupseteq (projx bb0) (projx bb0) /\ Isupseteq (projy bb0) (projy bb0).

Definition BBintersection (bb0 bb1 : BB) : BB :=
  (Iintersection (projx bb0) (projx bb1), Iintersection (projy bb0) (projy bb1)).

Definition BBarea (bb : BB) : Q :=
  width (projx bb) * width (projy bb).

Definition SetBB : Type := list BB.

(*Lemma foo : forall sbb, (exist bb, In bb sbb /\ isEmpty bb) -> isEmpty sbb. *) 

(* TODO: filter empty BB for efficiency *)
Fixpoint _BB_SBBintersection (bb : BB) (sbb accum : SetBB) : SetBB :=
  match sbb with
  | nil => accum
  | cons bb' sbb' => _BB_SBBintersection bb sbb' (cons (BBintersection bb bb') accum)
  end.

Fixpoint _SBBintersection (sbb0 sbb1 accum : SetBB) : SetBB :=
  match sbb0 with
  | nil => accum
  | cons bb sbb => _SBBintersection sbb sbb1 (_BB_SBBintersection bb sbb1 nil ++ accum)
  end.


Definition SBBintersection (sbb0 sbb1 : SetBB) : SetBB :=
  _SBBintersection sbb0 sbb1 nil.

Definition SBBunion (sbb0 sbb1 : SetBB) : SetBB :=
  sbb0 ++ sbb1.

Definition BB2area (bb0 bb1 : BB) : Q :=
  BBarea bb0 + BBarea bb1 - BBarea (BBintersection bb0 bb1).

Fixpoint _SetBBarea (sbb accum : SetBB) (area : Q) : Q :=
  match sbb with
  | nil => area
  | cons bb sbb' =>
    let sbb'' := _BB_SBBintersection bb accum nil in
    let sbb''area := List.fold_right Qplus 0 (List.map BBarea sbb'') in
    _SetBBarea sbb' (cons bb accum) (area + BBarea bb - sbb''area)
  end.

(* TODO wrong algorithm *)
Definition SetBBarea (sbb : SetBB) : Q :=
  _SetBBarea sbb nil 0.

(* TODO what happen at 0-divided ? *)
Definition RAT (sbb0 sbb1 : SetBB) : Q :=
  SetBBarea sbb0 / SetBBarea sbb1.

Inductive SBBexp : Set :=
  | EXP_SBBvar (x : string)
  | EXP_SBBintersection (sbb0 sbb1 : SBBexp) | EXP_SBBunion (sbb0 sbb1 : SBBexp)
  | EXP_makeSBB (bbs : list BBexp)
with BBexp : Set :=
  | EXP_BBvar (x : string)
  | EXP_makeBB (x y : Iexp)
  (* 画像全体のBB *)
  | EXP_BBimg
with Iexp : Set :=
  | EXP_Ivar (x : string)
  | EXP_projx (bb : BBexp) | EXP_projy (bb : BBexp)
  | EXP_Iintersection (i0 i1 : Iexp)
  | EXP_makeI (l u : Qexp)
with Qexp : Set :=
  | EXP_Q (a: Q)
  | EXP_Qvar (x : string)
  | EXP_width (i : Iexp) | EXP_RAT (sbb0 sbb1 : SBBexp)
  | EXP_projl (i : Iexp) | EXP_proju (i : Iexp)
  | EXP_projxl (bb : BBexp) | EXP_projxu (bb : BBexp)
  | EXP_projyl (bb : BBexp) | EXP_projyu (bb : BBexp).

Inductive Bexp : Set :=
  | EXP_Bvar (x : string)
  | EXP_not (b : Bexp) | EXP_and (b0 b1 : Bexp) | EXP_or (b0 b1 : Bexp)
  | EXP_BBeq (bb0 bb1 : BBexp)
  | EXP_BBoverlap (bb0 bb1 : BBexp)
  | EXP_BBsubset (bb0 bb1 : BBexp) | EXP_BBsupset (bb0 bb1 : BBexp)
  | EXP_BBsubseteq (bb0 bb1 : BBexp) | EXP_BBsupseteq (bb0 bb1 : BBexp)
  | EXP_Ilt (i0 i1 : Iexp) | EXP_Igt (i0 i1 : Iexp) | EXP_Ieq (i0 i1 : Iexp)
  | EXP_Ioverlap (i0 i1 : Iexp)
  | EXP_Iin (q : Qexp) (i : Iexp) | EXP_Iinrev (i : Iexp) (q : Qexp)
  | EXP_Isubset (i0 i1 : Iexp) | EXP_Isupset (i0 i1 : Iexp)
  | EXP_Isubseteq (i0 i1 : Iexp) | EXP_Isupseteq (i0 i1 : Iexp)
  | EXP_Qlt (q0 q1 : Qexp) | EXP_Qgt (q0 q1 : Qexp) 
  | EXP_Qeq (q0 q1 : Qexp)
  | EXP_Qle (q0 q1 : Qexp) | EXP_Qge (q0 q1 : Qexp) 
  | EXP_forall (bound : string) (sbb : SBBexp) (b : Bexp)
  | EXP_exists (bound : string) (sbb : SBBexp) (b : Bexp).

Inductive Cond : Set :=
  | CND_None
  | CND (b : Bexp).

Inductive Def : Set :=
  | DEF_SBB (x : string) (sbb : SBBexp)
  | DEF_BB (x : string) (bb : BBexp)
  | DEF_I (x : string) (i : Iexp)
  | DEF_Q (x : string) (q : Qexp)
  | DEF_B (x : string) (b : Bexp).

Definition Case : Set := string * list Def * Bexp.

Definition Spec : Set := Cond * list Case.

Module Import M := FMapList.Make(String_as_OT).

Inductive Value : Type :=
  | Vb (x : Prop) | Vq (x : Q) | Vi (x : Interval)
  | Vbb (x : BB) | Vsbb (x : SetBB).

Definition Env := M.t Value.

Fixpoint Asbb (expr : SBBexp) (env : Env) : option SetBB :=
  match expr with
  | EXP_SBBvar s =>
    match find s env with
    | Some (Vsbb sbb) => Some sbb
    | _ => None
    end
  | EXP_SBBintersection sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (SBBintersection sbb0 sbb1)
    | _, _ => None
    end
  | EXP_SBBunion sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (SBBunion sbb0 sbb1)
    | _, _ => None
    end
  | EXP_makeSBB bb_exprs =>
    List.fold_left (fun obbs obb =>
      match obbs, obb with
      | Some bbs, Some bb => Some (cons bb bbs)
      | _, _ => None
      end
    ) (List.map (fun bb_expr => Abb bb_expr env) bb_exprs) (Some nil)
  end
with Abb (expr : BBexp) (env : Env) : option BB :=
  match expr with
  | EXP_BBimg =>
    match find "IMG" env with
    | Some (Vbb bb) => Some bb
    | _ => None
    end
  | EXP_BBvar s =>
    match find s env with
    | Some (Vbb bb) => Some bb
    | _ => None
    end
  | EXP_makeBB i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (i0, i1)
    | _, _ => None
    end
  end
with Ai (expr : Iexp) (env : Env) : option Interval :=
  match expr with
  | EXP_Ivar s =>
    match find s env with
    | Some (Vi i) => Some i
    | _ => None
    end
  | EXP_projx bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projx bb)
    | None => None
    end
  | EXP_projy bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projy bb)
    | None => None
    end
  | EXP_Iintersection i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Iintersection i0 i1)
    | _, _ => None
    end
  | EXP_makeI q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0, q1)
    | _, _ => None
    end
  end

with Aq (expr : Qexp) (env : Env) : option Q :=
  match expr with
  | EXP_Q a => Some a
  | EXP_Qvar s =>
    match find s env with
    | Some (Vq q) => Some q
    | _ => None
    end
  | EXP_width i_expr =>
    match Ai i_expr env with
    | Some i => Some (width i)
    | None => None
    end
  | EXP_RAT sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (RAT sbb0 sbb1)
    | _, _ => None
    end
  | EXP_projl i_expr =>
    match Ai i_expr env with
    | Some i => Some (lower i)
    | _ => None
    end
  | EXP_proju i_expr =>
    match Ai i_expr env with
    | Some i => Some (upper i)
    | _ => None
    end
  | EXP_projxl bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projxl bb)
    | None => None
    end
  | EXP_projxu bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projxu bb)
    | None => None
    end
  | EXP_projyl bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projyl bb)
    | None => None
    end
  | EXP_projyu bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projyu bb)
    | None => None
    end
  end.

Definition option_and (a b : option Prop) : option Prop :=
    match a, b with
    | Some a, Some b => Some (a /\ b)
    | _, _ => None
    end.

Definition option_or (a b : option Prop) : option Prop :=
    match a, b with
    | Some a, Some b => Some (a \/ b)
    | _, _ => None
    end.

Fixpoint B (expr : Bexp) (env : Env) : option Prop :=
  match expr with
  | EXP_Bvar s =>
    match find s env with
    | Some (Vb b) => Some b
    | _ => None
    end
  | EXP_not b_expr =>
    match B b_expr env with
    | Some b => Some (not b)
    | None => None
    end
  | EXP_and b_expr0 b_expr1 =>
    match B b_expr0 env, B b_expr1 env with
    | Some b0, Some b1 => Some (b0 /\ b1)
    | _, _ => None
    end
  | EXP_or b_expr0 b_expr1 =>
    match B b_expr0 env, B b_expr1 env with
    | Some b0, Some b1 => Some (b0 \/ b1)
    | _, _ => None
    end
  | EXP_BBeq bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBeq bb0 bb1)
    | _, _ => None
    end
  | EXP_BBoverlap bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBoverlap bb0 bb1)
    | _, _ => None
    end
  | EXP_BBsubset bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBsubset bb0 bb1)
    | _, _ => None
    end
  | EXP_BBsupset bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBsupset bb0 bb1)
    | _, _ => None
    end
  | EXP_BBsubseteq bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBsubseteq bb0 bb1)
    | _, _ => None
    end
  | EXP_BBsupseteq bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBsupseteq bb0 bb1)
    | _, _ => None
    end
  | EXP_Ilt i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ilt i0 i1)
    | _, _ => None
    end
  | EXP_Igt i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Igt i0 i1)
    | _, _ => None
    end
  | EXP_Ieq i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ieq i0 i1)
    | _, _ => None
    end
  | EXP_Ioverlap i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ioverlap i0 i1)
    | _, _ => None
    end
  | EXP_Iin q_expr i_expr =>
    match Aq q_expr env, Ai i_expr env with
    | Some q, Some i => Some (Iin q i)
    | _, _ => None
    end
  | EXP_Iinrev i_expr q_expr =>
    match Aq q_expr env, Ai i_expr env with
    | Some q, Some i => Some (Iin q i)
    | _, _ => None
    end
  | EXP_Isubset i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isubset i0 i1)
    | _, _ => None
    end
  | EXP_Isupset i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isupset i0 i1)
    | _, _ => None
    end
  | EXP_Isubseteq i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isubseteq i0 i1)
    | _, _ => None
    end
  | EXP_Isupseteq i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isupseteq i0 i1)
    | _, _ => None
    end
  | EXP_Qlt q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0 < q1)%Q
    | _, _ => None
    end
  | EXP_Qgt q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0 < q1)%Q
    | _, _ => None
    end
  | EXP_Qeq q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0 = q1)
    | _, _ => None
    end
  | EXP_Qle q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0 <= q1)%Q
    | _, _ => None
    end
  | EXP_Qge q_expr0 q_expr1 =>
    match Aq q_expr0 env, Aq q_expr1 env with
    | Some q0, Some q1 => Some (q0 <= q1)%Q
    | _, _ => None
    end
  | EXP_forall bound sbb_expr b_expr =>
    match Asbb sbb_expr env with
    | Some sbb => List.fold_left option_and (List.map (fun bb => B b_expr env) sbb) (Some True)
    | _ => None
    end
  | EXP_exists bound sbb_expr b_expr =>
    match Asbb sbb_expr env with
    | Some sbb => List.fold_left option_or (List.map (fun bb => B b_expr env) sbb) (Some False)
    | _ => None
    end
  end.

Definition Ccond (cond : Cond) (env : Env) : option Prop :=
  match cond with
  | CND_None => Some True
  | CND b => B b env
  end.

Definition Cdef (def : Def) (env : Env) : option Env :=
  match def with
  | DEF_SBB s sbb_expr =>
    match Asbb sbb_expr env with
    | Some sbb => Some (add s (Vsbb sbb) env)
    | _ => None
    end
  | DEF_BB s bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (add s (Vbb bb) env)
    | _ => None
    end
  | DEF_I s i_expr =>
    match Ai i_expr env with
    | Some i => Some (add s (Vi i) env)
    | _ => None
    end
  | DEF_Q s q_expr =>
    match Aq q_expr env with
    | Some q => Some (add s (Vq q) env)
    | _ => None
    end
  | DEF_B s b_expr =>
    match B b_expr env with
    | Some b => Some (add s (Vb b) env)
    | _ => None
    end
  end.

Fixpoint Cdefs (defs : list Def) (env : Env) : option Env :=
  match defs with
  | nil => Some env
  | cons def defs' =>
    match Cdef def env with
    | Some env' => Cdefs defs' env'
    | _ => None
    end
  end.

Definition Ccase (case : Case) (env : Env) : option (string * Prop) :=
  match case with
  | (l, defs, b_expr) =>
    match Cdefs defs env with
    | Some env' =>
      match B b_expr env' with
      | Some b => Some (l, b)
      | _ => None
      end
    | _ => None
    end
  end.

Fixpoint Ccases (cases : list Case) (env : Env) (accum : list (string * Prop)) : option (list (string * Prop)) :=
  match cases with
  | nil => Some accum
  | cons case cases' =>
    match Ccase case env with
    | Some lb => Ccases cases' env (cons lb accum)
    | _ => None
    end
  end.

Definition Cspec (spec : Spec) (env : Env) : option (list (string * Prop)) :=
  match spec with
  | (cond, cases) =>
    match Ccond cond env, Ccases cases env nil with
    | Some b, Some lbs => Some (List.map
          (fun lb => match lb with (l, b') => (l, b /\ b') end)
          lbs)
    | _, _ => None
    end
  end.

Definition testEnv := add "q1" (Vq 1) (add "q0" (Vq 0) (empty Value)).

Lemma foo : B (EXP_Qlt (EXP_Qvar "q0") (EXP_Qvar "q1")) testEnv
  = match Aq (EXP_Qvar "q0") testEnv, Aq (EXP_Qvar "q1") testEnv with
    | Some q0, Some q1 => Some (q0 < q1)%Q
    | _, _ => None
  end.
Proof.
  simpl. trivial.
Qed.

Definition example_confluence : Spec := 
  ( CND_None
  , [ ( "シーン１"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_forall "x" (EXP_SBBvar "他車集合")
          (EXP_not (EXP_Ieq (EXP_projy (EXP_BBvar "x")) (EXP_Ivar "合流領域")))
      )
    ; ( "シーン２"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "x" (EXP_SBBvar "他車集合")
          (EXP_and
            (EXP_Qeq (EXP_projyl (EXP_BBvar "y")) (EXP_proju (EXP_Ivar "合流領域")))
            (EXP_forall "y" (EXP_SBBvar "他車集合")
              (EXP_or (EXP_not (EXP_Ieq (EXP_projy (EXP_BBvar "y")) (EXP_Ivar "合流領域")))
                      (EXP_BBeq (EXP_BBvar "x") (EXP_BBvar "y")))))
      )
    ; ( "シーン３"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "x" (EXP_SBBvar "他車集合")
         (EXP_and
           (EXP_Qeq (EXP_projyl (EXP_BBvar "x")) (EXP_proju (EXP_Ivar "合流領域")))
           (EXP_and
             (EXP_exists "y" (EXP_SBBvar "他車集合")
               (EXP_and
                 (EXP_Qeq (EXP_projyu (EXP_BBvar "y")) (EXP_projl (EXP_Ivar "合流領域")))
                 (EXP_not (EXP_BBeq (EXP_BBvar "x") (EXP_BBvar "y")))))
             (EXP_forall "z" (EXP_SBBvar "他車領域")
                   (EXP_not (EXP_Isupseteq (EXP_Ivar "合流領域") (EXP_projy (EXP_BBvar "z")))))))
      )
    ; ( "シーン４"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "z" (EXP_SBBvar "他車集合")
          (EXP_Isupseteq (EXP_Ivar "合流領域") (EXP_projy (EXP_BBvar "z")))
      )
    ]
  ).

Definition example_lead_vehicle_stopped : Spec :=
  ( CND (EXP_Bvar "前方車両がある")
  , [ ( "減速"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Ioverlap
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ; ( "停止"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Ilt
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ; ( "レスポンスなし"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Igt
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ]
  ).

Lemma or_falser : forall A : Prop, A \/ False <-> A.
Proof.
  intros. split.
  - intros. destruct H. assumption. contradiction. 
  - intros. apply (or_introl H).
Qed.

Lemma or_falsel : forall A : Prop, False \/ A <-> A.
Proof.
  intros.
  rewrite (or_comm False A).
  revert A.
  apply or_falser.
Qed.

Lemma and_l : forall A B : Prop, B -> (A /\ B <-> A).
Proof.
  intros. split.
  - intros. destruct H0. assumption.
  - intros. apply (conj H0 H).
Qed.

Proposition comprehensiveness_of_example_lead_vehicle_stopped :
  forall (exists_front : Prop) (front_bb dec : BB),
    let evaluated := 
      Cspec
        example_lead_vehicle_stopped
        (add "減速区間" (Vbb dec) (add "前方車両" (Vbb front_bb) (add "前方車両がある" (Vb exists_front) (empty Value))))
    in 
    BBisNotEmpty front_bb /\ BBisNotEmpty dec /\ exists_front ->
       match option_map (fun ev => List.fold_left or (List.map snd ev) False) evaluated with
       | Some b => b
       | _ => False
       end.
Proof.
  simpl. unfold BBisNotEmpty. unfold IisNotEmpty. unfold Igt. unfold Ilt.
  unfold Ioverlap. unfold IisEmpty. unfold Iintersection. unfold not.
  intros. destruct dec as (dec_x, dec_y). destruct front_bb as (f_x, f_y).
  destruct dec_x as (dec_xl, dec_xu). destruct dec_y as (dec_yl, dec_yu).
  destruct f_x as (f_xl, f_xu). destruct f_y as (f_yl, f_yu).
  simpl. simpl in H. destruct H. destruct H. destruct H0. destruct H0.
  rewrite (Q.min_lt_iff f_yu dec_yu (Qmax f_yl dec_yl)).
  rewrite (Q.max_lt_iff f_yl dec_yl dec_yu).
  rewrite (Q.max_lt_iff f_yl dec_yl f_yu).
  destruct (Qlt_le_dec dec_yu f_yl).
  - left. left. right. apply (conj H2 q).
  - destruct (Qlt_le_dec f_yu dec_yl).
  -- left. right. apply (conj H2 q0).
  -- right. split. assumption. intros. destruct H4. destruct H4.
  --- apply (Qle_lteq f_yl f_yu) in H1. destruct H1.
  ---- apply (Qlt_asym f_yl f_yu (conj H1 H4)).
  ---- rewrite H1 in H4. apply (Qlt_irrefl f_yu H4).
  --- apply (Qle_lteq dec_yl f_yu) in q0. destruct q0.
  ---- apply (Qlt_asym dec_yl f_yu (conj H5 H4)).
  ---- rewrite H5 in H4. apply (Qlt_irrefl f_yu H4).
  --- destruct H4.
  ---- apply (Qle_lteq f_yl dec_yu) in q. destruct q.
  ----- apply (Qlt_asym f_yl dec_yu (conj H5 H4)).
  ----- rewrite H5 in H4. apply (Qlt_irrefl dec_yu H4).
  ---- apply (Qle_lteq dec_yl dec_yu) in H3. destruct H3.
  ----- apply (Qlt_asym dec_yl dec_yu (conj H3 H4)).
  ----- rewrite H3 in H4. apply (Qlt_irrefl dec_yu H4).
Qed.

Definition example_debris_static_in_lane : Spec :=
  ( CND (EXP_Bvar "静的障害物がある")
  , [ ( "減速"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ; ( "停止"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Ilt (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ; ( "レスポンスなし"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Igt (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ]
  ).

Definition example_vehicle_cutting_in : Spec :=
  ( CND (EXP_and (EXP_Bvar "前方車両がある") (EXP_Bvar "他車両がある"))
  , [ ( "停止"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "自車線区間集合")
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))
      )
    ; ( "減速"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_forall "x" (EXP_SBBvar "自車線区間集合")
            (EXP_and
              (EXP_not (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x"))))
              (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))))
          (EXP_exists "x" (EXP_SBBvar "自車線区間")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))))
      )
    ; ( "前方車両に従う"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ]
      , EXP_Qlt (EXP_projyl (EXP_BBvar "前方車両")) (EXP_projyl (EXP_BBvar "割り込み車両"))
      )
    ; ( "割り込み車両に前方を譲る"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_forall "x" (EXP_SBBvar "自車線区間集合")
          (EXP_not
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_or
                (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ]
  ).

Definition example_vehicle_cutting_in_hwd : Spec :=
  ( CND (EXP_and (EXP_Bvar "前方車両がある") (EXP_Bvar "他車両がある"))
  , [ ( "右の車線に車線変更"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "他車両集合" (EXP_SBBvar "他車両集合")
        ; DEF_SBB "自車線左区間集合" (EXP_SBBvar "自車線左区間集合")
        ; DEF_SBB "自車線右区間集合" (EXP_SBBvar "自車線右区間集合")
        ; DEF_SBB "右車線変更区間集合" (EXP_SBBvar "右車線変更区間集合")
        ]
      , EXP_and
          (EXP_Bvar "右車線存在確認")
          (EXP_forall "x" (EXP_SBBvar "他車両集合")
            (EXP_exists "y" (EXP_SBBvar "右車線変更区間集合")
              (EXP_and
                (EXP_not (EXP_and
                  (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                  (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))
                (EXP_Qgt
                  (EXP_RAT
                    (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                    (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合")
                    (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                  (EXP_Q 1.0)))))
      )
    ; ( "左の車線に車線変更"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "他車両集合" (EXP_SBBvar "他車両集合")
        ; DEF_SBB "自車線左区間集合" (EXP_SBBvar "自車線左区間集合")
        ; DEF_SBB "自車線右区間集合" (EXP_SBBvar "自車線右区間集合")
        ; DEF_SBB "左車線変更区間集合" (EXP_SBBvar "左車線変更区間集合")
        ]
      , EXP_and
          (EXP_Bvar "左車線存在確認")
          (EXP_forall "x" (EXP_SBBvar "他車両集合")
            (EXP_exists "y" (EXP_SBBvar "左車線変更区間集合")
              (EXP_and
                (EXP_not (EXP_and
                  (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                  (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))
                (EXP_Qle
                  (EXP_RAT
                    (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                    (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合")
                    (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                  (EXP_Q 1.0)))))
      )
    ; ( "停止"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "他車両集合" (EXP_SBBvar "他車両集合")
        ; DEF_SBB "自車線左区間集合" (EXP_SBBvar "自車線左区間集合")
        ; DEF_SBB "自車線右区間集合" (EXP_SBBvar "自車線右区間集合")
        ; DEF_SBB "右車線変更区間集合" (EXP_SBBvar "右車線変更区間集合")
        ; DEF_SBB "左車線変更区間集合" (EXP_SBBvar "左車線変更区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_not
            (EXP_or
              (EXP_and
                (EXP_Bvar "右車線存在確認")
                (EXP_and
                  (EXP_forall "x" (EXP_SBBvar "他車両集合")
                    (EXP_exists "y" (EXP_SBBvar "右車線変更区間集合")
                      (EXP_not (EXP_and
                        (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                        (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))))
                  (EXP_Qgt
                    (EXP_RAT
                      (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                      (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                    (EXP_Q 1.0))))
              (EXP_and
                (EXP_Bvar "左車線存在確認")
                (EXP_and
                  (EXP_forall "x" (EXP_SBBvar "他車両集合")
                    (EXP_exists "y" (EXP_SBBvar "右車線変更区間集合")
                      (EXP_not (EXP_and
                        (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                        (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))))
                  (EXP_Qle
                    (EXP_RAT
                      (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                      (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                    (EXP_Q 1.0))))))
          (EXP_exists "x" (EXP_SBBunion (EXP_SBBvar "自車線右区間集合") (EXP_SBBvar "自車線左区間集合"))
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))))
      )
    ; ( "減速"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "他車両集合" (EXP_SBBvar "他車両集合")
        ; DEF_SBB "自車線左区間集合" (EXP_SBBvar "自車線左区間集合")
        ; DEF_SBB "自車線右区間集合" (EXP_SBBvar "自車線右区間集合")
        ; DEF_SBB "右車線変更区間集合" (EXP_SBBvar "右車線変更区間集合")
        ; DEF_SBB "左車線変更区間集合" (EXP_SBBvar "左車線変更区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_not
            (EXP_or
              (EXP_and
                (EXP_Bvar "右車線存在確認")
                (EXP_and
                  (EXP_forall "x" (EXP_SBBvar "他車両集合")
                    (EXP_exists "y" (EXP_SBBvar "右車線変更区間集合")
                      (EXP_not (EXP_and
                        (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                        (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))))
                  (EXP_Qgt
                    (EXP_RAT
                      (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                      (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                    (EXP_Q 1.0))))
              (EXP_and
                (EXP_Bvar "左車線存在確認")
                (EXP_and
                  (EXP_forall "x" (EXP_SBBvar "他車両集合")
                    (EXP_exists "y" (EXP_SBBvar "右車線変更区間集合")
                      (EXP_not (EXP_and
                        (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
                        (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))))))
                  (EXP_Qle
                    (EXP_RAT
                      (EXP_SBBintersection (EXP_SBBvar "自車線左区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ]))
                      (EXP_SBBintersection (EXP_SBBvar "自車線右区間集合") (EXP_makeSBB [ EXP_BBvar "割り込み車両" ])))
                    (EXP_Q 1.0))))))
          (EXP_and
            (EXP_forall "x" (EXP_SBBunion (EXP_SBBvar "自車線右区間集合") (EXP_SBBvar "自車線左区間集合"))
              (EXP_not (EXP_and
                (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
                (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))))
            (EXP_exists "x" (EXP_SBBunion (EXP_SBBvar "自車線右区間集合") (EXP_SBBvar "自車線左区間集合"))
              (EXP_and
                (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ; ( "前方車両に従う"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ]
      , EXP_Qlt (EXP_projyl (EXP_BBvar "前方車両")) (EXP_projyl (EXP_BBvar "割り込み車両"))
      )
    ; ( "割り込み車両に前方を譲る"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_forall "x" (EXP_SBBvar "自車線区間集合")
          (EXP_not
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_or
                (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ]
  ).

Definition example_ratio_relation1_2 : Spec :=
  ( CND_None
  , [ ( "割合の関係１(IoU=0.5の場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Qeq
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_SBBunion
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ])))
          (EXP_Q 0.5)
      )
    ; ( "割合の関係１(IoU=0.15の場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Qeq
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_SBBunion
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ])))
          (EXP_Q 0.15)
      )
    ]
  ).

Definition example_rational_relation3_4 : Spec :=
  ( CND_None
  , [ ( "割合の関係３(IoU=0.12かつAの右上の頂点とBの左下の頂点が重なっている場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0.5))
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
      )
    ; ( "割合の関係３(IoU=0.12かつAの右下の頂点とBの左上の頂点が重なっている場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0.5))
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
      )
    ]
  ).

Definition example_positional_relation1_2 : Spec :=
  ( CND_None
  , [ ( "位置関係１(AよりもBの方が上にある)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Ilt (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))
      )
    ; ( "位置関係１(AよりもBの方が右にある)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Ilt (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B"))
      )
    ]
  ).

Definition example_positional_relation3_4 : Spec :=
  ( CND (EXP_Bvar "画像全体を取得可能")
  , [ ( "位置関係３(BがAの左上と上の領域どちらともに位置している)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Ilt (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
          (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
      )
    ; ( "位置関係４(B全体の0.3以上がAの左下に位置している)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ; DEF_BB "A左下" (EXP_makeBB
          (EXP_makeI (EXP_projxl EXP_BBimg) (EXP_projxl (EXP_BBvar "A")))
          (EXP_makeI (EXP_projyl EXP_BBimg) (EXP_projyl (EXP_BBvar "A"))))
        ]
      , EXP_Qge
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A左下" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 0.3)
      )
    ]
  ).

Definition example_inclusion_relation1_2 : Spec :=
  ( CND_None
  , [ ( "包含関係１(BがAに包含されている)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ; ( "包含関係２(AがBに包含されている)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_BBsubseteq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ]
  ).

Definition example_comparison_relation1_2 : Spec :=
  ( CND_None
  , [ ( "大小関係１(AよりBが小さい)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_Qgt
          (EXP_RAT (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 1.0)
      )
    ; ( "大小関係２(AよりBが大さい)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_Qlt
          (EXP_RAT (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 1.0)
      )
    ]
  ).

Definition example_contains : Spec :=
  ( CND_None
  , [ ( "A contains B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
         (EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B"))
         (EXP_not (EXP_or
           (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
           (EXP_or
             (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
             (EXP_or
               (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
               (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B")))))))
      )
    ; ( "A covers B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
         (EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B"))
         (EXP_or
           (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
           (EXP_or
             (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
             (EXP_or
               (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
               (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B"))))))
      )
    ; ( "A touch B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0))
          (EXP_or
            (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
            (EXP_or
              (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
              (EXP_or
              (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
              (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B"))))))
      )
    ; ( "A overlapbdyintersect B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_not (EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_Q 1))
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_Q 0)))
      )
    ; ( "A equal B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_BBeq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ; ( "A disjoint B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_not (EXP_BBoverlap (EXP_BBvar "A") (EXP_BBvar "B"))
      )
    ; ( "A overlapbdydisjoint B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_or
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projy (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_and
                (EXP_Iin (EXP_projxl (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
                (EXP_Iin (EXP_projxu (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B"))))
              (EXP_and
                (EXP_Iin (EXP_projxu (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
                (EXP_not (EXP_Iin (EXP_projxl (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))))))
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projx (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_and
                (EXP_Iin (EXP_projyl (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
                (EXP_Iin (EXP_projyu (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
              (EXP_and
                (EXP_Iin (EXP_projyu (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
                (EXP_not (EXP_Iin (EXP_projyl (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))))))
      )
    ; ( "A on B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_or
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projy (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_Iinrev (EXP_projy (EXP_BBvar "B")) (EXP_projyu (EXP_BBvar "A")))
              (EXP_Iinrev (EXP_projy (EXP_BBvar "B")) (EXP_projyl (EXP_BBvar "A")))))
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projx (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_Iinrev (EXP_projx (EXP_BBvar "B")) (EXP_projxu (EXP_BBvar "A")))
              (EXP_Iinrev (EXP_projx (EXP_BBvar "B")) (EXP_projxl (EXP_BBvar "A")))))
      )
    ]
  ).