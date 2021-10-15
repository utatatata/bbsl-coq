Require Import ClassicalDescription QArith OrdersFacts QOrderedType Qminmax GenericMinMax String Bool List FMapList OrderedTypeEx Bool.
Import ListNotations.

Declare Scope BBSL_scope.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope Q_scope.
Local Open Scope list_scope.

Local Open Scope BBSL_scope.


(******************** Helpers ********************)

(*
(* use classical facts *)
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
Lemma not_Ioverlap_lt_gt : forall i0 i1, ~Iempty i0 /\ ~Iempty i1 -> ~Ioverlap i0 i1 <-> Ilt i0 i1 \/ Igt i0 i1.
Proof.
  unfold Ioverlap. unfold Iempty. unfold Iintersection. unfold Ilt. unfold Igt.
  intros. destruct i0. destruct i1. simpl.
  rewrite (DNE (Qmin q0 q2 < Qmax q q1)%Q).
  simpl in H. unfold not in H.  destruct H.
  rewrite (Qmin_lt_max_iff q0 q2 q q1).
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
*)

Lemma nor_nandn : forall A B, ~(A \/ B) -> ~A /\ ~B.
Proof.
  unfold not. intros A B H. split.
  - intro. destruct H. now apply or_introl.
  - intro. destruct H. now apply or_intror.
Qed.

Lemma Qeq_sym_iff : forall x y, (x == y)%Q <-> (y == x)%Q.
Proof.
  intros.
  split. q_order. q_order.
Qed.

Lemma Qlt_asym : forall x y, ~((x < y)%Q /\ (y < x)%Q).
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

Lemma Qmin_ltl_comm : forall x y z, (Qmin x y < z)%Q <-> (Qmin y x < z)%Q.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_ltr_comm : forall x y z, (z < Qmin x y)%Q <-> (z < Qmin x y)%Q.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_lel_comm : forall x y z, (Qmin x y <= z)%Q <-> (Qmin y x <= z)%Q.
Proof.
  intros. now rewrite Q.min_comm.
Qed.

Lemma Qmin_ler_comm : forall x y z, (z <= Qmin x y)%Q <-> (z <= Qmin y x)%Q.
Proof.
  intros. now rewrite  Q.min_comm.
Qed.

Lemma Qmax_ltl_comm : forall x y z, (Qmax x y < z)%Q <-> (Qmax y x < z)%Q.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_ltr_comm : forall x y z, (z < Qmax x y)%Q <-> (z < Qmax y x)%Q.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_lel_comm : forall x y z, (Qmax x y <= z)%Q <-> (Qmax y x <= z)%Q.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qmax_ler_comm : forall x y z, (z <= Qmax x y)%Q <-> (z <= Qmax y x)%Q.
Proof.
  intros. now rewrite Q.max_comm.
Qed.

Lemma Qlt_not_ge_iff : forall x y, x < y <-> ~y <= x.
Proof.
  intros. split. q_order. q_order.
Qed.

Lemma Qle_not_gt_iff : forall x y, x <= y <-> ~y < x.
Proof.
  intros. split. q_order. q_order.
Qed.

Lemma Qmin_lt_max_iff : forall x y z w, (Qmin x y < Qmax z w)%Q <-> ((x < z)%Q \/ (x < w)%Q) \/ (y < z)%Q \/ (y < w)%Q.
Proof.
  intros.
  now rewrite Q.min_lt_iff, Q.max_lt_iff, Q.max_lt_iff.
Qed.

Lemma Qmax_le_min_iff : forall x y z w, (Qmax x y <= Qmin z w)%Q <-> (x <= z /\ x <= w) /\ y <= z /\ y <= w.
Proof.
  intros x y z w.
  now rewrite Q.max_lub_iff, Q.min_glb_iff, Q.min_glb_iff.
Qed.

Lemma Qmin_le_max_iff : forall x y z w, (Qmin x y <= Qmax z w)%Q <-> (x <= z \/ x <= w) \/ y <= z \/ y <= w.
Proof.
  intros.
  now rewrite Q.min_le_iff, Q.max_le_iff, Q.max_le_iff.
Qed.

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

(* TODO unnecessary? *)
(*
Lemma toTrue : forall P : Prop, P -> P <-> True.
Proof.
  now intro P.
Qed.
*)

(*
Lemma norn_nand : forall A B, ~A \/ ~B -> ~(A /\ B).
Proof.
  unfold not. intros A B H. destruct H.
  intro HAandB. destruct HAandB as (HA & HB). contradiction.
  intro HAandB. destruct HAandB as (HA & HB). apply (H HB).
Qed.
*)

(*
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

Lemma or_truel : forall A : Prop, True \/ A <-> True.
Proof.
  intros. split.
  - intros. destruct H. trivial. trivial.
  - intros. apply (or_introl H).
Qed. 

Lemma or_truer : forall A : Prop, A \/ True <-> True.
Proof.
  intros.
  rewrite (or_comm A True).
  revert A.
  apply or_truel.
Qed.

Lemma and_truel : forall A : Prop, True /\ A <-> A.
Proof.
  intros. split.
  - intros. destruct H. trivial.
  - intros. split. trivial. trivial.
Qed.

Lemma and_truer : forall A : Prop, A /\ True <-> A.
Proof.
  intros.
  rewrite (and_comm A True).
  revert A.
  apply and_truel.
Qed.

Lemma and_l : forall A B : Prop, B -> (A /\ B <-> A).
Proof.
  intros. split.
  - intros. destruct H0. assumption.
  - intros. apply (conj H0 H).
Qed.

Lemma and_r : forall A B : Prop, A -> (A /\ B <-> B).
Proof.
  intros.
  rewrite (and_comm A B).
  revert H.
  apply and_l.
Qed.

Lemma or_l : forall A B : Prop, A -> (A \/ B <-> True).
Proof.
  intros. split.
  intros. trivial. intros. apply (or_introl H).
Qed.

Lemma or_r : forall A B : Prop, B -> (A \/ B <-> True).
Proof.
  intros. rewrite (or_comm A B).
  revert H. revert B A. apply or_l.
Qed.
*)



(******************** Interval ********************)

Definition Interval : Type := Q * Q.

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

Infix "==" := Ieq (at level 70, no associativity) : BBSL_scope.
Infix "<" := Ilt : BBSL_scope.
Infix "<=" := Ile : BBSL_scope.
Notation "x > y" := (Ilt y x)(only parsing) : BBSL_scope.
Notation "x >= y" := (Ile y x)(only parsing) : BBSL_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : BBSL_scope.

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

Lemma Iintersection_comm : forall i j, Iintersection i j == Iintersection j i.
Proof.
  unfold Iintersection, Ieq.
  simpl. intros.
  rewrite Q.max_comm, Q.min_comm.
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



(******************** Bounding Box ********************)

Definition BB : Type := Interval * Interval.

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

Infix "==" := BBeq (at level 70, no associativity) : BBSL_scope.

Lemma BBeq_refl : forall p, p == p.
Proof.
  unfold BBeq. intros. split.
  apply Ieq_refl. apply Ieq_refl.
Qed.

Lemma BBeq_sym_iff : forall p q, p == q <-> q == p.
Proof.
  unfold BBeq. destruct p as (px, py), q as (qx, _qy). simpl.
  now rewrite (Ieq_sym_iff qx px), (Ieq_sym_iff _qy py).
Qed.

Lemma BBeq_trans : forall p q r, p == q -> q == r -> p == r.
Proof.
  unfold BBeq. destruct p as (px, py), q as (qx, _qy), r as (rx, ry). simpl.
  intros H H0. destruct H, H0. split.
  - apply (Ieq_trans px qx rx H H0).
  - apply (Ieq_trans py _qy ry H1 H2). 
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
  unfold BBsubseteq. destruct p as (px, py), q as (qx, _qy), c as (cx, cy). simpl.
  intros H H0. destruct H as (H, H1), H0 as (H0, H2). split.
  - apply (Isubseteq_trans px qx cx H H0).
  - apply (Isubseteq_trans py _qy cy H1 H2).
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
  unfold BBsubset. destruct p as (px, py), q as (qx, _qy), r as (rx, ry). simpl.
  intros H H0. destruct H, H0.
  split. apply (Isubset_trans px qx rx H H0). apply (Isubset_trans py _qy ry H1 H2).
Qed.

Definition BBarea (p : BB) : Q :=
  width (projx p) * width (projy p).



(******************** Set of BB ********************)

Definition SetBB : Type := list BB.

(* TODO: filter empty BB for efficiency *)
Fixpoint _BB_SBBintersection (p : BB) (ps accum : SetBB) : SetBB :=
  match ps with
  | nil => accum
  | cons q qs => _BB_SBBintersection p qs (cons (BBintersection p q) accum)
  end.

Fixpoint _SBBintersection (ps qs accum : SetBB) : SetBB :=
  match ps with
  | nil => accum
  | cons p ps' => _SBBintersection ps' qs (_BB_SBBintersection p qs nil ++ accum)
  end.

Definition SBBintersection (ps qs : SetBB) : SetBB :=
  _SBBintersection ps qs nil.

Definition SBBunion (ps qs : SetBB) : SetBB :=
  ps ++ qs.

Fixpoint _SetBBarea (ps accum : SetBB) (area : Q) : Q :=
  match ps with
  | nil => area
  | cons p qs =>
    let cs := _BB_SBBintersection p accum nil in
    let csarea := List.fold_right Qplus 0 (List.map BBarea cs) in
    _SetBBarea qs (cons p accum) (area + BBarea p - csarea)
  end.

Definition SetBBarea (ps : SetBB) : Q :=
  _SetBBarea ps nil 0.

Definition RAT (ps qs : SetBB) : Q :=
  SetBBarea ps / SetBBarea qs.



(******************** Expressions ********************)

(* Set of bounding box *)
Inductive SBBexp : Set :=
  | EXP_SBBvar (s : string)
  | EXP_SBBintersection (ps qs : SBBexp) | EXP_SBBunion (ps qs : SBBexp)
  | EXP_makeSBB (ps : list BBexp)
(* Bouding box *)
with BBexp : Set :=
  | EXP_BBvar (s : string)
  | EXP_makeBB (i j : Iexp)
  (* 画像全体のBB *)
  | EXP_BBimg
(* Interval *)
with Iexp : Set :=
  | EXP_Ivar (s : string)
  | EXP_projx (p : BBexp) | EXP_projy (p : BBexp)
  | EXP_Iintersection (i j : Iexp)
  | EXP_makeI (x y : Qexp)
(* Rational number *)
with Qexp : Set :=
  | EXP_Q (x: Q)
  | EXP_Qvar (s : string)
  | EXP_width (i : Iexp) | EXP_RAT (ps qs : SBBexp)
  | EXP_projl (i : Iexp) | EXP_proju (i : Iexp)
  | EXP_projxl (p : BBexp) | EXP_projxu (p : BBexp)
  | EXP_projyl (p : BBexp) | EXP_projyu (p : BBexp).

(* Boolean *)
Inductive Bexp : Set :=
  | EXP_Bvar (s : string)
  | EXP_not (a : Bexp) | EXP_and (a b : Bexp) | EXP_or (a b : Bexp)
  | EXP_BBeq (p q : BBexp)
  | EXP_BBoverlap (p q : BBexp)
  | EXP_BBsubset (p q : BBexp) | EXP_BBsupset (p q : BBexp)
  | EXP_BBsubseteq (p q : BBexp) | EXP_BBsupseteq (p q : BBexp)
  | EXP_Ilt (i j : Iexp) | EXP_Igt (i j : Iexp) | EXP_Ieq (i j : Iexp)
  | EXP_Ioverlap (i j : Iexp)
  | EXP_Iin (x : Qexp) (i : Iexp) | EXP_Iinrev (i : Iexp) (x : Qexp)
  | EXP_Isubset (i j : Iexp) | EXP_Isupset (i j : Iexp)
  | EXP_Isubseteq (i j : Iexp) | EXP_Isupseteq (i j : Iexp)
  | EXP_Qlt (x y : Qexp) | EXP_Qgt (x y : Qexp) 
  | EXP_Qeq (x y : Qexp)
  | EXP_Qle (x y : Qexp) | EXP_Qge (x y : Qexp) 
  | EXP_forall (bound : string) (ps : SBBexp) (a : Bexp)
  | EXP_exists (bound : string) (ps : SBBexp) (a : Bexp).



(******************** Syntax ********************)

(* Condition block *)
Inductive Cond : Set :=
  | CND_None
  | CND (a : Bexp).

Inductive Def : Set :=
  | DEF_SBB (s : string) (ps : SBBexp)
  | DEF_BB (s : string) (p : BBexp)
  | DEF_I (s : string) (i : Iexp)
  | DEF_Q (s : string) (x : Qexp)
  | DEF_B (s : string) (a : Bexp).

(* Case block *)
Definition Case : Set := string * list Def * Bexp.

(* Whole of syntax *)
Definition Spec : Set := Cond * list Case.



(******************** Semantic functions ********************)

Module Import M := FMapList.Make(String_as_OT).

Inductive Value : Type :=
  | Vb (A : Prop) | Vq (x : Q) | Vi (i : Interval)
  | Vbb (p : BB) | Vsbb (ps : SetBB).

(* Environment: a set of string(a variable name) and value pairs  *)
Definition Env := M.t Value.

(* Set of bounding box *)
Fixpoint Asbb (expr : SBBexp) (env : Env) : option SetBB :=
  match expr with
  | EXP_SBBvar s =>
    match find s env with
    | Some (Vsbb ps) => Some ps
    | _ => None
    end
  | EXP_SBBintersection expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (SBBintersection ps qs)
    | _, _ => None
    end
  | EXP_SBBunion expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (SBBunion ps qs)
    | _, _ => None
    end
  | EXP_makeSBB expr_ps =>
    List.fold_left (fun option_ps option_p =>
      match option_ps, option_p with
      | Some ps, Some p => Some (cons p ps)
      | _, _ => None
      end
    ) (List.map (fun expr_p => Abb expr_p env) expr_ps) (Some nil)
  end
(* Bounding box *)
with Abb (expr : BBexp) (env : Env) : option BB :=
  match expr with
  | EXP_BBimg =>
    match find "IMG" env with
    | Some (Vbb p) => Some p
    | _ => None
    end
  | EXP_BBvar s =>
    match find s env with
    | Some (Vbb p) => Some p
    | _ => None
    end
  | EXP_makeBB expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i, j)
    | _, _ => None
    end
  end
(* Interval *)
with Ai (expr : Iexp) (env : Env) : option Interval :=
  match expr with
  | EXP_Ivar s =>
    match find s env with
    | Some (Vi i) => Some i
    | _ => None
    end
  | EXP_projx expr_p =>
    match Abb expr_p env with
    | Some p => Some (projx p)
    | None => None
    end
  | EXP_projy expr_p =>
    match Abb expr_p env with
    | Some p => Some (projy p)
    | None => None
    end
  | EXP_Iintersection expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Iintersection i j)
    | _, _ => None
    end
  | EXP_makeI expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x, y)
    | _, _ => None
    end
  end
(* Rational number *)
with Aq (expr : Qexp) (env : Env) : option Q :=
  match expr with
  | EXP_Q x => Some x
  | EXP_Qvar s =>
    match find s env with
    | Some (Vq x) => Some x
    | _ => None
    end
  | EXP_width expr_i =>
    match Ai expr_i env with
    | Some i => Some (width i)
    | None => None
    end
  | EXP_RAT expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (RAT ps qs)
    | _, _ => None
    end
  | EXP_projl expr_i =>
    match Ai expr_i env with
    | Some i => Some (lower i)
    | _ => None
    end
  | EXP_proju expr_i =>
    match Ai expr_i env with
    | Some i => Some (upper i)
    | _ => None
    end
  | EXP_projxl expr_p =>
    match Abb expr_p env with
    | Some p => Some (projxl p)
    | None => None
    end
  | EXP_projxu expr_p =>
    match Abb expr_p env with
    | Some p => Some (projxu p)
    | None => None
    end
  | EXP_projyl expr_p =>
    match Abb expr_p env with
    | Some p => Some (projyl p)
    | None => None
    end
  | EXP_projyu expr_p =>
    match Abb expr_p env with
    | Some p => Some (projyu p)
    | None => None
    end
  end.

(* Boolean *)
Fixpoint B (expr : Bexp) (env : Env) : option Prop :=
  match expr with
  | EXP_Bvar s =>
    match find s env with
    | Some (Vb a) => Some a
    | _ => None
    end
  | EXP_not expr_a =>
    match B expr_a env with
    | Some b => Some (not b)
    | None => None
    end
  | EXP_and expr_a expr_b =>
    match B expr_a env, B expr_b env with
    | Some a, Some b => Some (a /\ b)
    | _, _ => None
    end
  | EXP_or expr_a expr_b =>
    match B expr_a env, B expr_b env with
    | Some a, Some b => Some (a \/ b)
    | _, _ => None
    end
  | EXP_BBeq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (p == b)
    | _, _ => None
    end
  | EXP_BBoverlap expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBoverlap p b)
    | _, _ => None
    end
  | EXP_BBsubset expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsubset p b)
    | _, _ => None
    end
  | EXP_BBsupset expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsupset p b)
    | _, _ => None
    end
  | EXP_BBsubseteq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsubseteq p b)
    | _, _ => None
    end
  | EXP_BBsupseteq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsupseteq p b)
    | _, _ => None
    end
  | EXP_Ilt expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i < j)
    | _, _ => None
    end
  | EXP_Igt expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i > j)
    | _, _ => None
    end
  | EXP_Ieq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Ieq i j)
    | _, _ => None
    end
  | EXP_Ioverlap expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Ioverlap i j)
    | _, _ => None
    end
  | EXP_Iin expr_x expr_i =>
    match Aq expr_x env, Ai expr_i env with
    | Some x, Some i => Some (Iin x i)
    | _, _ => None
    end
  | EXP_Iinrev expr_i expr_x =>
    match Aq expr_x env, Ai expr_i env with
    | Some x, Some i => Some (Iin x i)
    | _, _ => None
    end
  | EXP_Isubset expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isubset i j)
    | _, _ => None
    end
  | EXP_Isupset expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isupset i j)
    | _, _ => None
    end
  | EXP_Isubseteq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isubseteq i j)
    | _, _ => None
    end
  | EXP_Isupseteq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isupseteq i j)
    | _, _ => None
    end
  | EXP_Qlt expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x < y)%Q
    | _, _ => None
    end
  | EXP_Qgt expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x < y)%Q
    | _, _ => None
    end
  | EXP_Qeq expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x = y)
    | _, _ => None
    end
  | EXP_Qle expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x <= y)%Q
    | _, _ => None
    end
  | EXP_Qge expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x <= y)%Q
    | _, _ => None
    end
  | EXP_forall bound expr_ps expr_a =>
    match Asbb expr_ps env with
    | Some ps => List.fold_left option_and (List.map (fun p => B expr_a (add bound (Vbb p) env)) ps) (Some True)
    | _ => None
    end
  | EXP_exists bound expr_ps expr_a =>
    match Asbb expr_ps env with
    | Some ps => List.fold_left option_or (List.map (fun p => B expr_a (add bound (Vbb p) env)) ps) (Some False)
    | _ => None
    end
  end.

(* Condition block *)
Definition Ccond (cond : Cond) (env : Env) : option Prop :=
  match cond with
  | CND_None => Some True
  | CND a => B a env
  end.

Definition Cdef (def : Def) (env : Env) : option Env :=
  match def with
  | DEF_SBB s expr_ps =>
    match Asbb expr_ps env with
    | Some ps => Some (add s (Vsbb ps) env)
    | _ => None
    end
  | DEF_BB s expr_p =>
    match Abb expr_p env with
    | Some p => Some (add s (Vbb p) env)
    | _ => None
    end
  | DEF_I s expr_i =>
    match Ai expr_i env with
    | Some i => Some (add s (Vi i) env)
    | _ => None
    end
  | DEF_Q s expr_x =>
    match Aq expr_x env with
    | Some x => Some (add s (Vq x) env)
    | _ => None
    end
  | DEF_B s expr_a =>
    match B expr_a env with
    | Some a => Some (add s (Vb a) env)
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
  | (label, defs, expr_a) =>
    match Cdefs defs env with
    | Some env' =>
      match B expr_a env' with
      | Some a => Some (label, a)
      | _ => None
      end
    | _ => None
    end
  end.

(* Case block *)
Fixpoint Ccases (cases : list Case) (env : Env) (accum : list (string * Prop)) : option (list (string * Prop)) :=
  match cases with
  | nil => Some accum
  | cons case cases' =>
    match Ccase case env with
    | Some label_bool => Ccases cases' env (cons label_bool accum)
    | _ => None
    end
  end.

(* Whole of syntax *)
Definition Cspec (spec : Spec) (env : Env) : option (list (string * Prop)) :=
  match spec with
  | (cond, cases) =>
    match Ccond cond env, Ccases cases env nil with
    | Some a, Some label_bools => Some (List.map
          (fun label_bool => match label_bool with (label, b) => (label, a /\ b) end)
          label_bools)
    | _, _ => None
    end
  end.
