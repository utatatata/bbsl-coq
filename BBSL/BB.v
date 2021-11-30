Require Import QArith.
Require Import BBSL.Interval.


Definition BB : Type := Interval * Interval.

Declare Scope BB_scope.
Open Scope BB_scope.

Definition projx (p : BB) : Interval :=
  match p with
  | (px, _) => px
  end.

Definition projy (p : BB) : Interval :=
  match p with
  | (_, py) => py
  end.

Definition projxl (p : BB) : Q :=
  lower (projx p).

Definition projxu (p : BB) : Q :=
  upper (projx p).

Definition projyl (p : BB) : Q :=
  lower (projy p).

Definition projyu (p : BB) : Q :=
  upper (projy p).

Definition BBempty (p : BB) : Prop :=
  Iempty (projx p) \/ Iempty (projy p).

Definition BBnempty (p : BB) : Prop :=
  Inempty (projx p) /\ Inempty (projy p).

Definition BBeq (p q : BB) : Prop :=
  projx p == projx q /\ projy p == projy q.

Infix "==" := BBeq (at level 70, no associativity) : BB_scope.

Lemma BBeq_refl : forall p, p == p.
Proof.
  unfold BBeq. intros. split.
  apply Ieq_refl. apply Ieq_refl.
Qed.

Lemma BBeq_comm : forall p q, p == q <-> q == p.
Proof.
  unfold BBeq. destruct p as (px, py), q as (qx, qy). simpl.
  now rewrite (Ieq_comm qx px), (Ieq_comm qy py).
Qed.

Lemma BBeq_trans : forall p q r, p == q -> q == r -> p == r.
Proof.
  unfold BBeq. destruct p as (px, py), q as (qx, qy), r as (rx, ry). simpl.
  intros H H0. destruct H, H0. split.
  - apply (Ieq_trans px qx rx H H0).
  - apply (Ieq_trans py qy ry H1 H2). 
Qed.

Definition BBoverlap (p q : BB) : Prop :=
  Ioverlap (projx p) (projx q) /\ Ioverlap (projy p) (projy q).

Definition BBsubset (p q : BB) :=
  Isubset (projx p) (projx q) /\ Isubset (projy p) (projy q).
Definition BBsubseteq (p q : BB) :=
  Isubseteq (projx p) (projx q) /\ Isubseteq (projy p) (projy q).
Notation BBsupset p q := (BBsubset q p) (only parsing).
Notation BBsupseteq p q := (BBsubseteq q p) (only parsing).

Lemma BBsubseteq_refl : forall p, BBsubseteq p p.
Proof.
  unfold BBsubseteq.
  split. apply Isubseteq_refl. apply Isubseteq_refl.
Qed.

Lemma BBsubseteq_antisym : forall p q, BBsubseteq p q -> BBsubseteq q p -> p == q.
Proof.
  unfold BBsubseteq, BBeq. destruct p, q. simpl.
  intros. split.
  - now apply Isubseteq_antisym.
  - now apply Isubseteq_antisym.
Qed.

Lemma BBsubseteq_trans : forall p q c, BBsubseteq p q -> BBsubseteq q c -> BBsubseteq p c.
Proof.
  unfold BBsubseteq. destruct p as (px, py), q as (qx, qy), c as (cx, cy). simpl.
  intros H H0. destruct H as (H, H1), H0 as (H0, H2). split.
  - apply (Isubseteq_trans px qx cx H H0).
  - apply (Isubseteq_trans py qy cy H1 H2).
Qed.

Definition BBintersection (p q : BB) : BB :=
  (Iintersection (projx p) (projx q), Iintersection (projy p) (projy q)).

Lemma BBsubseteq_intersection : forall p q,
  BBsubseteq (BBintersection p q) p /\ BBsubseteq (BBintersection p q) q.
Proof.
  unfold BBsubseteq, BBintersection.
  destruct p, q. simpl.
  split.
  - split. apply Isubseteq_intersection. apply Isubseteq_intersection.
  - split. apply Isubseteq_intersection. apply Isubseteq_intersection.
Qed.

Lemma BBsubset_irrefl : forall p, BBnempty p -> ~BBsubset p p.
Proof.
  unfold BBnempty, BBsubset. destruct p as (px, py). simpl.
  intros H H0. destruct H, H0.
  apply (Isubset_irrefl px H H0).
Qed.

Lemma BBsubset_trans : forall p q r, BBsubset p q -> BBsubset q r -> BBsubset p r.
Proof.
  unfold BBsubset. destruct p as (px, py), q as (qx, qy), r as (rx, ry). simpl.
  intros H H0. destruct H, H0.
  split. apply (Isubset_trans px qx rx H H0). apply (Isubset_trans py qy ry H1 H2).
Qed.

Definition BBarea (p : BB) : Q :=
  width (projx p) * width (projy p).
