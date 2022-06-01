Require Import Arith.


(** * Definition of [Interval] *)

(** Intervals are pairs of lower bounds and upper bounds. *)

Definition Interval : Type := { lb_ub : nat * nat | fst lb_ub <= snd lb_ub }.

Declare Scope Interval_scope.
Open Scope Interval_scope.

Definition lb (i : Interval) : nat := match i with exist _ lb_ub p => fst lb_ub end.
Definition ub (i : Interval) : nat := match i with exist _ lb_ub jp => snd lb_ub end.


(** * Basic relations of ICC (Interval connection calculus) *)

(** disconnected *)
Definition dcleft i j := ub i < lb j.
Notation dcright i j := (dcleft j i) (only parsing).
Notation dc i j := (dcleft i j \/ dcright i j) (only parsing).

Definition ecleft i j := ub i = lb j.
Notation ecright i j := (ecleft j i) (only parsing).
(** externally connected *)
Notation ec i j := (ecleft i j \/ ecright i j) (only parsing).

(** equal *)
Definition eq i j := lb i = lb j /\ ub i = ub j.

(** partially overlapping *)
Definition poleft i j := lb i < lb j /\ lb j < ub i /\ ub i < ub j.
Notation poright i j := (poleft j i) (only parsing).
Notation po i j := (poleft i j \/ poright i j) (only parsing).

(** tangential proper part *)
Definition tppleft i j := lb i = lb j /\ ub i < ub j.
Definition tppright i j := lb j < lb i /\ ub i = ub j.
Notation tpp i j := (tppleft i j \/ tppright i j) (only parsing).

(** tangential proper part inverse *)
Notation tppileft i j := (tppleft j i) (only parsing).
Notation tppiright i j := (tppright j i) (only parsing).
Notation tppi i j := (tpp j i) (only parsing).

(** non-tangential proper part *)
Definition ntpp i j := lb j < lb i /\ ub i < ub j.

(** non-tangential proper part inverse *)
Notation ntppi i j := (ntpp j i) (only parsing).

(** proper part *)
Definition pp i j := tpp i j \/ ntpp i j.

(** non-proper part *)
Definition npp i j := pp i j \/ eq i j.

(** overlapping *)
Definition overlap i j :=
  ec i j \/ eq i j \/ po i j \/ tpp i j \/ tppi i j \/ ntpp i j \/ ntppi i j.

(** Aliases *)
Notation lt i j := (dcleft i j) (only parsing).
Notation subset i j := (pp i j) (only parsing).
Notation subseteq i j := (npp i j) (only parsing).
Notation gt i j := (lt j i) (only parsing).
Notation supset i j := (subset j i) (only parsing).
Notation supseteq i j := (subseteq j i) (only parsing).

Infix "==" := eq (at level 70, no associativity) : Interval_scope.
Infix "<" := lt : Interval_scope.
Notation "x > y" := (lt y x)(only parsing) : Interval_scope.
Notation "x < y < z" := (x<y/\y<z) : Interval_scope.


#[global]
Hint Unfold dcleft ecleft eq poleft tppleft tppright ntpp pp npp overlap : iarith.
#[global]
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.


(** * Decidability *)

Theorem icc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { eq i j } + { ntppi i j } +
  { tppileft i j } + { ntpp i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
Proof.
  unfold dcleft, ecleft, poleft, tppright, tppleft, eq, ntpp.
  destruct i as ((lbi, ubi), p), j as ((lbj, ubj), q). simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ubi lbj). destruct s.
  (* dcleft (ubi < lbj) *)
  - now left; left; left; left; left; left; left; left; left; left; left; left.
  (* ecleft (ubi = lbj) *)
  - now left; left; left; left; left; left; left; left; left; left; left; right.
  - destruct (lt_eq_lt_dec lbi lbj), (lt_eq_lt_dec ubi ubj). destruct s, s0.
  (* poleft (lbi < lbj < ubi /\ lbj < ubi < ubj) *)
  -- left; left; left; left; left; left; left; left; left; left; right.
     repeat split. assumption. assumption. assumption.
  (* tppiright (lbi < lbj /\ ubi = lbj) *)
  -- left; left; left; left; left; left; left; left; left; right.
     split. assumption. now apply eq_sym.
  (* tppleft (lbi = lbj /\ ubi < ubj) *)
  -- left; left; left; left; left; left; left; left; right.
     split. assumption. assumption.
  (* eq (lbi = lbj /\ ubi = ubj) *)
  -- left; left; left; left; left; left; left; right.
     split. assumption. assumption.
  -- destruct s.
  (* ntppi (lbi < lbj /\ ubj < ubi) *)
  --- left; left; left; left; left; left; right.
      split. assumption. assumption.
  (* tppileft (lbj = lbi /\ ubj < ubi) *)
  --- left; left; left; left; left; right.
      split. now apply eq_sym. assumption.
  -- destruct s.
  (* ntpp (lbj < lbi /\ ubi < ubj) *)
  --- left; left; left; left; right.
      split. assumption. assumption.
  (* tppright (lbj < lbi /\ ubi = ubj) *)
  --- left; left; left; right.
      split. assumption. assumption.
  -- destruct (lt_eq_lt_dec lbi ubj). destruct s.
  (* poright (lbj < lbi < ubj < ubi) *)
  --- left; left; right.
      repeat split. assumption. assumption. assumption.
  (* ecright (lbj = ubi) *)
  --- left; right. now apply eq_sym.
  (* dcright (lbi < ubj) *)
  --- right. assumption.
Qed.

(*
Lemma dcleft_not_ecleft : forall i j, dcleft i j -> ~ecleft i j.
Proof.
  unfold dcleft, ecleft, not.
  intros. Nat.order.
Qed.

Lemma dcleft_not_poleft : forall i j, dcleft i j -> ~poleft i j.
Proof.
  unfold dcleft, poleft, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, (H1, H2)). Nat.order.
Qed.

Lemma dcleft_not_tppiright : forall i j, dcleft i j -> ~tppiright i j.
Proof.
  unfold dcleft, tppiright, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_tppleft : forall i j, dcleft i j -> ~tppleft i j.
Proof.
  unfold dcleft, tppleft, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_eq : forall i j, dcleft i j -> ~eq i j.
Proof.
  unfold dcleft, eq, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_ntppi : forall i j, dcleft i j -> ~ntppi i j.
Proof.
  unfold dcleft, ntppi, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_tppileft : forall i j, dcleft i j -> ~tppileft i j.
Proof.
  unfold dcleft, tppileft, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_ntpp : forall i j, dcleft i j -> ~ntpp i j.
Proof.
  unfold dcleft, ntpp, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_tppright : forall i j, dcleft i j -> ~tppright i j.
Proof.
  unfold dcleft, tppright, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_poright : forall i j, dcleft i j -> ~poright i j.
Proof.
  unfold dcleft, poright, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H (H0, H1). Nat.order.
Qed.

Lemma dcleft_not_ecright : forall i j, dcleft i j -> ~ecright i j.
Proof.
  unfold dcleft, ecright, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H H0. Nat.order.
Qed.

Lemma dcleft_not_dcright : forall i j, dcleft i j -> ~dcright i j.
Proof.
  unfold dcleft, dcright, not. intros (i, p) (j, q). simpl in p, q. simpl.
  intros H H0. Nat.order.
Qed.
*)


(** * properties of basic relations *)

Theorem dcleft_irrefl : forall i, ~i < i.
Proof.
  auto with iarith.
  unfold dcleft. intros (i, p). simpl. now apply le_not_lt.
Qed.

Theorem dcleft_asym : forall i j, i < j -> ~j < i.
Proof.
  unfold dcleft. intros (i, p) (j, q). simpl. Nat.order.
Qed.

Theorem dcleft_trans : forall i j k, i < j -> j < k -> i < k.
Proof.
  unfold dcleft. intros (i, p) (j, q) (k, r). simpl. Nat.order.
Qed.

Lemma dcleft_eq : forall i j k, i < j -> j == k -> i < k.
Proof.
  unfold dcleft, eq. intros (i, p) (j, q) (k, r). simpl. intros H (H0, H1). Nat.order.
Qed.

Lemma eq_dcleft : forall i j k, i == j -> j < k -> i < k.
Proof.
  unfold dcleft, eq. intros (i, p) (j, q) (k, r). simpl. intros (H, H0). Nat.order.
Qed.

Theorem dc_irrefl : forall i, ~dc i i.
Proof.
  intros i [H | H]. apply (dcleft_irrefl i H). apply (dcleft_irrefl i H).
Qed.

Theorem dc_sym : forall i j, dc i j -> dc j i.
Proof.
  intros i j [H | H]. now right. now left.
Qed.

(** ecleft has no theorems *)

Theorem eq_refl : forall i, i == i.
Proof.
  unfold eq. split. apply eq_refl. apply eq_refl.
Qed.

Theorem eq_sym : forall i j, i == j -> j == i.
Proof.
  unfold eq. intros i j (H, H0). split.
  apply (sym_equal H). apply (sym_equal H0).
Qed.

Lemma eq_sym_iff : forall i j, i == j <-> j == i.
Proof.
  split. apply eq_sym. apply eq_sym.
Qed.

Theorem eq_trans : forall i j k, i == j -> j == k -> i == k.
Proof.
  unfold eq. intros i j k (H, H0) (H1, H2). split.
  apply (eq_trans H H1). apply (eq_trans H0 H2).
Qed.

Theorem eq_dec : forall i j, {i == j} + {~ i == j}.
Proof.
  unfold eq. destruct i as ((lbi, ubi), p), j as ((lbj, ubj), q). simpl in p, q. simpl.
  destruct (Nat.eq_dec lbi lbj), (Nat.eq_dec ubi ubj).
  - left. split. assumption. assumption.
  - right. intros (H, H0). apply (n H0).
  - right. intros (H, H0). apply (n H).
  - right. intros (H, H0). apply (n H).
Qed.

Theorem no_eq_sym i j : ~ i == j -> ~ j == i.


Theorem poleft_irrefl : forall i, ~poleft i i.
Proof.
  unfold poleft. intros (i, p). simpl. intros (H, H0). apply (lt_irrefl (fst i) H).
Qed.

Theorem poleft_asym : forall i j, poleft i j -> ~poleft j i.
Proof.
  unfold poleft. intros (i, p) (j, q). simpl. intros (H, H0) (H1, H2). Nat.order.
Qed.

Theorem po_irrefl : forall i, ~po i i.
Proof.
  intros i [H | H]. apply (poleft_irrefl i H). apply (poleft_irrefl i H).
Qed.

Theorem po_sym : forall i j, po i j -> po j i.
Proof.
  intros. rewrite or_comm. assumption.
Qed.

Theorem tppleft_irrefl : forall x, ~tppleft x x.
Proof.
  unfold tppleft. intros (i, p). simpl. intros (H, H0). apply (lt_irrefl (snd i) H0).
Qed.

Theorem tppleft_asym : forall i j, tppleft i j -> ~tppleft j i.
Proof.
  unfold tppleft. intros (i, p) (j, q). simpl. intros (H, H0) (H1, H2). Nat.order.
Qed.

Theorem tppleft_trans : forall i j k, tppleft i j -> tppleft j k -> tppleft i k.
Proof.
  unfold tppleft. intros (i, p) (j, q) (k, r). simpl. intros (H, H0) (H1, H2).
  split. apply (Nat.eq_trans H H1). apply (Nat.lt_trans (snd i) (snd j) (snd k) H0 H2).
Qed.

Theorem tppright_irrefl : forall i, ~tppright i i.
Proof.
  unfold tppright. intros (i, p). simpl. intros (H, H0). apply (lt_irrefl (fst i) H).
Qed.

Theorem tppright_asym : forall i j, tppright i j -> ~tppright j i.
  unfold tppright. intros (i, p) (j, q). simpl. intros (H, H0) (H1, H2). Nat.order.
Qed.

Theorem tppright_trans : forall i j k, tppright i j -> tppright j k -> tppright i k.
Proof.
  unfold tppright. intros (i, p) (j, q) (k, r). simpl. intros (H, H0) (H1, H2).
  split. apply (lt_trans (fst k) (fst j) (fst i) H1 H). apply (Nat.eq_trans H0 H2).
Qed.

Theorem tpp_irrefl : forall i, ~tpp i i.
Proof.
  intros i [H | H]. apply (tppleft_irrefl i H). apply (tppright_irrefl i H).
Qed.

(*
Lemma tppleft_not_tppright : forall i j, tppleft i j -> ~tppright i j.
Proof.
  unfold tppleft, tppright, not. intros  (i, p) (j, q). simpl in p, q. simpl.
  intros (H, H0) (H1, H2). Nat.order.
Qed.
*)

Theorem tpp_asym : forall i j, tpp i j -> ~tpp j i.
Proof.
  unfold tppleft, tppright. intros (i, p) (j, q). simpl in p, q. simpl.
  intros [(H, H0) | (H, H0)] [(H1, H2) | (H1, H2)].
  Nat.order. Nat.order. Nat.order. Nat.order.
Qed.

Theorem ntpp_irrefl : forall i, ~ntpp i i.
Proof.
  unfold ntpp. intros i (H, H0). apply (lt_irrefl (lb i) H).
Qed.

Theorem ntpp_asym : forall i j, ntpp i j -> ~ntpp j i.
Proof.
  unfold ntpp. intros i j (H, H0) (H1, H2). Nat.order.
Qed.

Theorem ntpp_trans : forall i j k, ntpp i j -> ntpp j k -> ntpp i k.
  unfold ntpp. intros i j k (H, H0) (H1, H2). split. Nat.order. Nat.order.
Qed.

Theorem pp_irrefl : forall i, ~pp i i.
Proof.
  unfold pp. intros i [H | H].
  apply (tpp_irrefl i H). apply (ntpp_irrefl i H).
Qed.

Theorem pp_asym : forall i j, pp i j -> ~pp j i.
Proof.
  unfold pp, tppleft, tppright, ntpp. intros (i, p) (j, q). simpl in p, q. simpl.
  intros [[(H, H0) | (H, H0)] | (H, H0)] [[(H1, H2) | (H1, H2)] | (H1, H2)].
  Nat.order. Nat.order. Nat.order. Nat.order. Nat.order.
  Nat.order. Nat.order. Nat.order. Nat.order.
Qed.

Theorem pp_trans : forall i j k, pp i j -> pp j k -> pp i k.
Proof.
  unfold pp, tppleft, tppright, ntpp.
  intros i j k [[(H, H0) | (H, H0)] | (H, H0)] [[(H1, H2) | (H1, H2)] | (H1, H2)].
  - left. left. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - left. right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
Qed.

Lemma pp_eq : forall i j k, pp i j -> j == k -> pp i k.
Proof.
  intros i j k H H0.
  rewrite H0 in H.

  unfold pp, eq, tppleft, tppright, ntpp.
  intros i j k [[(H, H0) | (H, H0)] | (H, H0)] (H1, H2).
  - left. left. split. Nat.order. Nat.order.
  - left. right. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
Qed.

Lemma eq_pp : forall i j k, i == j -> pp j k -> pp i k.
Proof.
  unfold pp, eq. intros (i, p) (j, q) (k, r). simpl.
  intros (H, H0) [(H1, H2) | (H1, H2)].
  - left. split. Nat.order. Nat.order.
  - right. split. Nat.order. Nat.order.
Qed.

Theorem npp_refl : forall x, npp x x.
Proof.
  unfold npp. intros x. right. now apply eq_sym.
Qed.

Theorem npp_antisym : forall x y, npp x y -> npp y x -> x == y.
Proof.
  unfold npp. intros x y [H | H] [H0 | H0].
  - now apply pp_asym in H.
  - now apply eq_sym.
  - assumption.
  - assumption.
Qed.

Theorem npp_trans : forall x y z, npp x y -> npp y z -> npp x z.
Proof.
  unfold npp. intros x y z [H | H] [H0 | H0].
  - left. apply (pp_trans x y z H H0).
  - left. apply (pp_eq x y z H H0).
  - left. apply (eq_pp x y z H H0).
  - right. apply (eq_trans x y z H H0).
Qed.

Lemma npp_pp_eq : forall i j, npp i j -> pp i j \/ i == j.
Proof.
  unfold npp, pp. intros i j [[H | H] | H].
  - now left; left.
  - now left; right.
  - now right.
Qed.

Notation npp_pp_eq := npp_pp_eq (only parsing).

Theorem overlap_refl : forall i, overlap i i.
Proof.
  unfold overlap. intros i. left. apply npp_refl.
Qed.

Theorem overlap_sym : forall i j, overlap i j -> overlap j i.
Proof.
  unfold overlap. intros i j.
  unfold overlap, pp, eq. intros (i, p) (j, q). simpl. intros [(H, H0)|[(H, H0)|[(H, H0)|[(H, H0)|(H,H0)]]]].
  - right. left. split. Nat.order. Nat.order.
  - left. split. Nat.order. Nat.order.
  - right. right. left. split. Nat.order. Nat.order.
  - destruct (le_lt_dec (snd i) (snd j)).
  -- right. right. right. right. split. Nat.order. Nat.order.
  -- 
  right. right. right. right. split. Nat.order. Nat.order.
  - right. right. right. right. split. Nat.order. right. right. right. right. split. Nat.order.
  - right. left. split. Nat.order. Nat.order.
  - left. right. split. Nat.order. Nat.order.
  - right. right. split. Nat.order. Nat.order.
  - right. right. split. Nat.order. Nat.order.
  - left. left. split. Nat.order. Nat.order.
  - left. right. split. Nat.order. Nat.order.
  - right. left. split. Nat.order. Nat.order.
  -



(*
Lemma porigh_not_rcc : forall i j, poright i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros ((H, H0), H1). repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H2, H3), H4). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma ecrigh_not_rcc : forall i j, ecright i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros H. repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
Qed.

Lemma dcrigh_not_rcc : forall i j, dcright i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros H. repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
Qed.

Lemma pp_not_rcc : forall i j, pp i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold pp, tpp. intros i j [[H | H] | H].
  - apply tppleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption. assumption.
  - apply tppright_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption. assumption.
  - apply ntpp_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption. assumption.
Qed.

Lemma npp_not_rcc : forall i j, npp i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~ntppi i j /\
  ~tppileft i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold npp. intros i j [H | H].
  - apply pp_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, H8))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption.
  - apply eq_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption.
Qed.

Lemma overlap_not_lt_gt : forall i j, overlap i j -> ~lt i j /\ ~gt i j.
Proof.
  unfold overlap. intros i j [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]].
  - apply ecleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply ecleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply eq_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply poleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply poleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply tppleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply tppleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply tppright_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply tppright_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply ntpp_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
  - apply ntpp_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    split. assumption. assumption.
Qed.

Lemma dcleft_not_rcc : forall i j, dcleft i j ->
  ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros H. repeat split.
  - Nat.order.
  - intros ((H0, H1), H2). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma eq_not_rcc : forall i j, eq i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros (H, H0). repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma dc_not_rcc : forall i j, dc i j ->
  ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j.
Proof.
  unfold dc. intros i j [H | H].
  - apply dcleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption. assumption.
  - apply dcleft_not_rcc in H.
    destruct H as (H, (H0, (H1, (H2, (H3, (H4, (H5, (H6, (H7, (H8, (H9, H10))))))))))).
    repeat split.
    assumption. assumption. assumption. assumption.
    intros H11. apply (eq_sym i j) in H11.
    assumption. assumption.
    assumption. assumption. assumption. assumption. assumption.

Lemma ecleft_not_rcc : forall i j, ecleft i j ->
  ~dcleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros H. repeat split.
  - Nat.order.
  - intros ((H0, H1), H2). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - intros (H0, H1). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma poleft_not_rcc : forall i j, poleft i j ->
  ~dcleft i j /\ ~ecleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros ((H, H0), H1). repeat split.
  - Nat.order.
  - Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros (H2, H3). Nat.order.
  - intros ((H2, H3), H4). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma tppleft_not_rcc : forall i j, tppleft i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros (H, H0). repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma tppright_not_rcc : forall i j, tppright i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~ntpp i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros (H, H0). repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.

Lemma ntpp_not_rcc : forall i j, ntpp i j ->
  ~dcleft i j /\ ~ecleft i j /\ ~poleft i j /\
  ~tppiright i j /\ ~tppleft i j /\ ~eq i j /\ ~ntppi i j /\
  ~tppileft i j /\ ~tppright i j /\
  ~poright i j /\ ~ecright i j /\ ~dcright i j.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft, eq, ntppi, tppileft,
         ntpp, tppright, poright, ecright, dcright, not.
  intros (i, p) (j, q). simpl. intros (H, H0). repeat split.
  - Nat.order.
  - Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros (H1, H2). Nat.order.
  - intros ((H1, H2), H3). Nat.order.
  - Nat.order.
  - Nat.order.
Qed.
*)

(*
Definition lt_irrefl := dcleft_irrefl.
Definition lt_asym := dcleft_asym.
Definition lt_trans := dcleft_trans.
Definition lt_eq := dcleft_eq.
Definition eq_lt := eq_dcleft.
*)

Lemma lt_overlap_lt_dec : forall i j, { i < j } + { overlap i j } + { j < i }.

Lemma intersection_comm : forall i j (H : overlap i j), intersection i j H == intersection j i H.

(* operators *)

Definition intersection (i j : Interval) : overlap i j -> Interval.
  (*destruct i as (i, p), j as (j, q). simpl. intros H. simpl in H.*)
  intros H. destruct H.
  assert (max (fst i) (fst j) < min (snd i) (snd j))%nat.
  rewrite Nat.max_lub_lt_iff, Nat.min_glb_lt_iff, Nat.min_glb_lt_iff.
  destruct H as [H | H]. (*destruct H. [(H, H0)|(H, H0)].*)
  repeat split. Nat.order. Nat.order. Nat.order. Nat.order.
  repeat split. Nat.order. Nat.order. Nat.order. Nat.order.
  exact (exist _ (max (fst i) (fst j), min (snd i) (snd j)) H0).
Qed.
