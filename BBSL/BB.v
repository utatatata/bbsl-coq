Require Import QArith.
Require Import BBSL.Interval.

Open Scope Interval_scope.

(** * Definition of [BB] **)

Definition BB : Type := Interval * Interval.

Declare Scope BB_scope.
Bind Scope BB_scope with BB.
Delimit Scope BB_scope with BB.
Open Scope BB_scope.

Definition projx : BB -> Interval := fst.
Definition projy : BB -> Interval := snd.
Definition projxl (a : BB) := lb (projx a).
Definition projxu (a : BB) := ub (projx a).
Definition projyl (a : BB) := lb (projy a).
Definition projyu (a : BB) := ub (projy a).

(** Basic relations of BB. **)

Definition BBeq a b := projx a == projx b /\ projy a == projy b.
Definition BBsubseteq a b := 
  Isubseteq (projx a) (projx b) /\ Isubseteq (projy a) (projy b).
Definition BBoverlap a b :=
  Ioverlap (projx a) (projx b) /\ Ioverlap (projy a) (projy b).
Definition BBintersection (a b : BB) : BBoverlap a b -> BB.
  unfold BBoverlap. destruct a as (ax, ay), b as (bx, _by). simpl.
  intros (H, H0).
  exact (Iintersection ax bx H, Iintersection ay _by H0).
Defined.
(*
Definition BBsubset a b :=
  ((projxl b) <= (projxl a))%nat /\ ((projxu a) < (projxu b))%nat /\
  ((projyl b) < (projyl a))%nat /\ ((projyu a) < (projyu b))%nat \/

  ((projxl b) < (projxl a))%nat /\ ((projxu a) <= (projxu b))%nat /\
  ((projyl b) < (projyl a))%nat /\ ((projyu a) < (projyu b))%nat \/

  ((projxl b) < (projxl a))%nat /\ ((projxu a) < (projxu b))%nat /\
  ((projyl b) <= (projyl a))%nat /\ ((projyu a) < (projyu b))%nat \/

  ((projxl b) < (projxl a))%nat /\ ((projxu a) < (projxu b))%nat /\
  ((projyl b) < (projyl a))%nat /\ ((projyu a) <= (projyu b))%nat.
*)
(*
Notation Isupset a b := (Isubset b a) (only parsing).
*)
Notation Isupseteq a b := (Isubseteq b a) (only parsing).

Infix "==" := BBeq (at level 70, no associativity) : BB_scope.


(** * Decidability *)

Theorem BBeq_dec : forall a b, {a == b} + {~ a == b}.
Proof.
  unfold BBeq. intros (ax, ay) (bx, _by). simpl.
  destruct (Ieq_dec ax bx), (Ieq_dec ay _by).
  - left. split. assumption. assumption.
  - right. intros (H, H1). apply (n H1).
  - right. intros (H, H1). apply (n H).
  - right. intros (H, H1). apply (n H).
Qed.


(** * Properties of basic relations *)

Lemma BBeq_refl : forall a, a == a.
Proof.
  unfold BBeq. split.
  apply Ieq_refl. apply Ieq_refl.
Qed.

Lemma BBeq_sym : forall a b, a == b -> b == a.
Proof.
  unfold BBeq. intros (ax, ay) (bx, _by). simpl.
  intros (Hax_eq_bx, Hay_eq_by). split.
  now apply Ieq_sym. now apply Ieq_sym.
Qed.

Lemma BBeq_sym_iff : forall a b, a == b <-> b == a.
Proof.
  split. apply BBeq_sym. apply BBeq_sym.
Qed.

Lemma BBeq_trans : forall a b c, a == b -> b == c -> a == c.
Proof.
  unfold BBeq.
  intros (ax, ay) (bx, _by) (cx, cy). simpl.
  intros (Hax_eq_bx, Hay_eq_by) (Hbx_eq_cx, Hby_eq_cy). split.
  apply (Ieq_trans ax bx cx Hax_eq_bx Hbx_eq_cx).
  apply (Ieq_trans ay _by cy Hay_eq_by Hby_eq_cy).
Qed.

(*
Lemma BBsubset_irrefl : forall a, ~BBsubset a a.
Proof.
  unfold BBsubset, projxl, projxu, projyl, projyu.
  intros (((axl, axu), axp), ((ayl, ayu), ayp)). simpl in axp, ayp. simpl.
  intros [(H, (H0, (H1, H2))) | [(H, (H0, (H1, H2))) |
         [(H, (H0, (H1, H2))) | (H, (H0, (H1, H2)))]]].
  - now apply (Nat.lt_irrefl axu).
  - now apply (Nat.lt_irrefl ayl).
  - now apply (Nat.lt_irrefl axu).
  - now apply (Nat.lt_irrefl axu).
Qed.

Lemma BBsubset_trans : forall a b c, BBsubset a b -> BBsubset b c -> BBsubset a c.
Proof.
  unfold BBsubset, projxl, projxu, projyl, projyu.
  intros (((axl, axu), axp), ((ayl, ayu), ayp))
         (((bxl, bxu), bxp), ((byl, byu), byp))
         (((cxl, cxu), cxp), ((cyl, cyu), cyp)).
  simpl in axp, ayp, bxp, byp, cxp, cyp. simpl.
  intros [(H, (H0, (H1, H2))) | [(H, (H0, (H1, H2))) |
         [(H, (H0, (H1, H2))) | (H, (H0, (H1, H2)))]]]
         [(H3, (H4, (H5, H6))) | [(H3, (H4, (H5, H6))) |
         [(H3, (H4, (H5, H6))) | (H3, (H4, (H5, H6)))]]].
  - left. repeat split.
    now apply (Nat.le_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; left. repeat split.
    now apply (Nat.lt_le_trans cxl bxl axl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; left. repeat split.
    now apply (Nat.lt_le_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; right. repeat split.
    now apply (Nat.lt_le_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans ayu byu cyu).

  - left. repeat split.
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cxl bxl axl).
    now apply (Nat.le_lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.le_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.le_lt_trans axu bxu cxu).
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; right. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.le_lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans ayu byu cyu).

  - left. repeat split.
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_le_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans axu bxu cxu).
    now apply (Nat.lt_le_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.le_trans cyl byl ayl).
    now apply (Nat.lt_trans ayu byu cyu).
  - right; right; right. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_le_trans cyl byl ayl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans ayu byu cyu).

  - left. repeat split.
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.le_lt_trans ayu byu cyu).
  - right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    apply Nat.lt_eq_cases. left. now apply (Nat.lt_le_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.le_lt_trans ayu byu cyu).
  - right; right; left. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    apply Nat.lt_eq_cases. left. now apply (Nat.le_lt_trans cyl byl ayl).
    now apply (Nat.le_lt_trans ayu byu cyu).
  - right; right; right. repeat split.
    now apply (Nat.lt_trans cxl bxl axl).
    now apply (Nat.lt_trans axu bxu cxu).
    now apply (Nat.lt_trans cyl byl ayl).
    now apply (Nat.le_trans ayu byu cyu).
Qed.
*)

Lemma BBsubseteq_refl : forall a, BBsubseteq a a.
Proof.
  unfold BBsubseteq. intros (ax, ay). simpl. split.
  apply Isubseteq_refl. apply Isubseteq_refl.
Qed.

Lemma BBsubseteq_antisym : forall a b,
  BBsubseteq a b -> BBsubseteq b a -> a == b.
Proof.
  unfold BBsubseteq, BBeq. intros (ax, ay) (bx, _by). simpl.
  intros (H, H0) (H1, H2). split.
  now apply Isubseteq_antisym. now apply Isubseteq_antisym.
Qed.

Lemma BBsubseteq_trans : forall a b c,
  BBsubseteq a b -> BBsubseteq b c -> BBsubseteq a c.
Proof.
  unfold BBsubseteq. intros (ax, ay) (bx, _by) (cx, cy). simpl.
  intros (H, H0) (H1, H2). split.
  apply (Isubseteq_trans ax bx cx H H1). apply (Isubseteq_trans ay _by cy H0 H2).
Qed.

Lemma BBoverlap_refl : forall a, BBoverlap a a.
Proof.
  unfold BBoverlap. intros (ax, ay). simpl. split.
  apply Ioverlap_refl. apply Ioverlap_refl.
Qed.

Lemma BBoverlap_sym : forall a b, BBoverlap a b -> BBoverlap b a.
Proof.
  unfold BBoverlap. intros (ax, ay) (bx, _by). simpl.
  intros (H, H1). split. now apply Ioverlap_sym. now apply Ioverlap_sym.
Qed.

Lemma BBintersection_comm : forall a b (Haob : BBoverlap a b) (Hboa : BBoverlap b a),
  BBintersection a b Haob == BBintersection b a Hboa.
Proof.
  unfold BBintersection, BBeq, BBoverlap, projx. intros (ax, ay) (bx, _by). simpl.
  intros (H, H0) (H1, H2).  simpl. split.
  apply (Iintersection_comm ax bx H H1).
  apply (Iintersection_comm ay _by H0 H2).
Qed.

(*
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
*)
