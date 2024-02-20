Require Import Arith.


(** ** Definition of Interval algebra
 * half-open interval (right-open)
 * X = { a | left X <= a < right X} (left X < right X)
 *)
Definition Interval : Type := { tupl | fst tupl < snd tupl }.

Declare Scope Interval_scope.
Bind Scope Interval_scope with Interval.
Delimit Scope Interval_scope with Interval.
Open Scope Interval_scope.

(** left/right end-point *)
Definition left  (x : Interval) := match x with exist _ tuple _ => fst tuple end.
Definition right (x : Interval) := match x with exist _ tuple _ => snd tuple end.
Definition width (x : Interval) := right x - left x.



(** ** Basic relations of Interval algebra. *)
Definition precedes x y := right x < left y.
Definition meets    x y := right x = left y.
Definition overlaps x y := left x < left y /\ left y < right x < right y.
Definition starts   x y := left x = left y /\ right x < right y.
Definition during   x y := left y < left x /\ right x < right y.
Definition finishes x y := left y < left x /\ right x = right y.
Definition equal    x y := left x = left y /\ right x = right y.

Notation  preceded   x y := (precedes y x) (only parsing).
Notation  met        x y := (meets y x)    (only parsing).
Notation  overlapped x y := (overlaps y x) (only parsing).
Notation  started    x y := (starts y x)   (only parsing).
Notation  contains   x y := (during y x)   (only parsing).
Notation  finished   x y := (finishes y x) (only parsing).

Infix "==" := equal (at level 70, no associativity) : Interval_scope.
Infix "<" := precedes : Interval_scope.
Notation "x > y" := (precedes y x) (only parsing) : Interval_scope.
Notation "x < y < z" := (x < y /\ y < z) : Interval_scope.



(** ** Decidability of Interval algebra *)
Theorem ia_dec : forall x y,
  {precedes x y} + {preceded   x y} + {meets    x y} + {met      x y} +
  {overlaps x y} + {overlapped x y} + {starts   x y} + {started  x y} +
  {during   x y} + {contains   x y} + {finishes x y} + {finished x y} +
  {equal    x y}.
Proof.
  unfold precedes, meets, overlaps, finishes, starts, during, equal.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  destruct (lt_eq_lt_dec xr yl). destruct s.
  (* precedes (xr < yl) *)
  { do 12 left. assumption. }
  (* meets (xr = yl) *)
  { do 10 left; right. assumption. }
  destruct (lt_eq_lt_dec xl yl), (lt_eq_lt_dec xr yr). destruct s, s0.
  (* overlaps (xl < yl < xr < yr) *)
  { do 8 left; right. easy. }
  (* finished (xl < yl /\ xr = yr) *)
  { left; right. easy. }
  (* starts (xl = yl /\ xr < yr) *)
  { do 6 left; right. easy. }
  (* equal (xl = yl /\ xr = yr) *)
  { right. easy. }
  destruct s.
  (* contains (xl < yl /\ yr < xr) *)
  { do 3 left; right. easy. }
  (* started (xl = yl /\ yr < xr) *)
  { do 5 left; right. easy. }
  destruct s.
  (* during (yl < xl /\ xr < yr) *)
  { do 4 left; right. easy. }
  (* finishes (yl < xl /\ xr = yr) *)
  { do 2 left; right. easy. }
  destruct (lt_eq_lt_dec xl yr). destruct s.
  (* overlapped (yl < xl < yr < xr) *)
  { do 7 left; right. easy. }
  (* met (xl = yr) *)
  { do 9 left; right. easy. }
  (* preceded (yr < xl) *)
  { do 11 left; right. easy. }
Qed.



(** ** Properties of basic relations *)

Lemma precedes_asym : forall x y, x < y -> ~ y < x.
Proof.
  unfold precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H in p.
  rewrite q in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma meets_asym : forall x y, meets x y -> ~meets y x.
Proof.
  unfold meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H in p.
  rewrite H0 in q.
  rewrite q in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma overlaps_asym : forall x y, overlaps x y -> ~overlaps y x.
Proof.
  unfold overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl xl H).
Qed.
Lemma starts_asym : forall x y, starts x y -> ~starts y x.
Proof.
  unfold starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H2 in H0.
  apply (Nat.lt_irrefl xr H0).
Qed.
Lemma during_asym : forall x y, during x y -> ~during y x.
Proof.
  unfold during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl yl H).
Qed.
Lemma finishes_asym : forall x y, finishes x y -> ~finishes y x.
  unfold finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl xl H1).
Qed.
Lemma equal_sym_iff : forall x y, x == y <-> y == x.
Proof.
  unfold equal. easy.
Qed.



(** ** Exclusivity *)

Lemma precedes_not_meets : forall x y, x < y -> ~meets x y.
Proof.
  unfold precedes, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H0 in H.
  apply (Nat.lt_irrefl yl H).
Qed.
Lemma precedes_not_met : forall x y, x < y -> ~met x y.
Proof.
  unfold precedes, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H0 in q.
  rewrite q in H.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma precedes_not_overlaps : forall x y, x < y -> ~overlaps x y.
Proof.
  unfold precedes, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 [H1 H2]].
  rewrite H1 in H.
  apply (Nat.lt_irrefl xr H).
Qed.
Lemma precedes_not_overlapped : forall x y, x < y -> ~overlapped x y.
Proof.
  unfold precedes, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 [H1 H2]].
  rewrite H0 in H.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma precedes_not_starts : forall x y, x < y -> ~starts x y.
Proof.
  unfold precedes, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H0 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma precedes_not_started : forall x y, x < y -> ~started x y.
Proof.
  unfold precedes, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite <- H0 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma precedes_not_during : forall x y, x < y -> ~during x y.
Proof.
  unfold precedes, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma precedes_not_contains : forall x y, x < y -> ~contains x y.
Proof.
  unfold precedes, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in q.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma precedes_not_finishes : forall x y, x < y -> ~finishes x y.
Proof.
  unfold precedes, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in H.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma precedes_not_finished : forall x y, x < y -> ~finished x y.
  unfold precedes, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in q.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma precedes_not_equal : forall x y, x < y -> ~x == y.
  unfold precedes, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl yl p).
Qed.

Lemma meets_not_precedes : forall x y, meets x y -> ~x < y.
Proof.
  unfold meets, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H in H0.
  apply (Nat.lt_irrefl yl H0).
Qed.
Lemma meets_not_preceded : forall x y, meets x y -> ~x > y.
Proof.
  unfold meets, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H H0.
  rewrite H in p.
  rewrite q in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma meets_not_overlaps : forall x y, meets x y -> ~overlaps x y.
Proof.
  unfold meets, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 [H1 H2]].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma meets_not_overlapped : forall x y, meets x y -> ~overlapped x y.
Proof.
  unfold meets, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 [H1 H2]].
  rewrite H in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma meets_not_starts : forall x y, meets x y -> ~starts x y.
Proof.
  unfold meets, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H0 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma meets_not_started : forall x y, meets x y -> ~started x y.
Proof.
  unfold meets, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite <- H0 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma meets_not_during : forall x y, meets x y -> ~during x y.
Proof.
  unfold meets, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma meets_not_contains : forall x y, meets x y -> ~contains x y.
Proof.
  unfold meets, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in q.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma meets_not_finishes : forall x y, meets x y -> ~finishes x y.
Proof.
  unfold meets, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in H.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma meets_not_finished : forall x y, meets x y -> ~finished x y.
  unfold meets, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H1 in q.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma meets_not_equal : forall x y, meets x y -> ~x == y.
  unfold meets, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros H [H0 H1].
  rewrite H in p.
  rewrite H0 in p.
  apply (Nat.lt_irrefl yl p).
Qed.

Lemma overlaps_not_precedes : forall x y, overlaps x y -> ~x < y.
Proof.
  unfold overlaps, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] H2.
  rewrite H0 in H2.
  apply (Nat.lt_irrefl xr H2).
Qed.
Lemma overlaps_not_preceded : forall x y, overlaps x y -> ~x > y.
Proof.
  unfold overlaps, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] H2.
  rewrite H1 in p.
  rewrite H2 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma overlaps_not_meets : forall x y, overlaps x y -> ~meets x y.
Proof.
  unfold overlaps, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] H2.
  rewrite H2 in H0.
  apply (Nat.lt_irrefl yl H0).
Qed.
Lemma overlaps_not_met : forall x y, overlaps x y -> ~met x y.
Proof.
  unfold overlaps, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] H2.
  rewrite H1 in p.
  rewrite H2 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma overlaps_not_starts : forall x y, overlaps x y -> ~starts x y.
Proof.
  unfold overlaps, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl yl H).
Qed.
Lemma overlaps_not_started : forall x y, overlaps x y -> ~started x y.
Proof.
  unfold overlaps, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl xl H).
Qed.
Lemma overlaps_not_during : forall x y, overlaps x y -> ~during x y.
Proof.
  unfold overlaps, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma overlaps_not_contains : forall x y, overlaps x y -> ~contains x y.
Proof.
  unfold overlaps, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] [H2 H3].
  rewrite H3 in H1.
  apply (Nat.lt_irrefl xr H1).
Qed.
Lemma overlaps_not_finishes : forall x y, overlaps x y -> ~finishes x y.
Proof.
  unfold overlaps, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] [H2 H3].
  rewrite H3 in H1.
  apply (Nat.lt_irrefl yr H1).
Qed.
Lemma overlaps_not_finished : forall x y, overlaps x y -> ~finished x y.
  unfold overlaps, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] [H2 H3].
  rewrite H3 in H1.
  apply (Nat.lt_irrefl xr H1).
Qed.
Lemma overlaps_not_equal : forall x y, overlaps x y -> ~x == y.
  unfold overlaps, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H [H0 H1]] [H2 H3].
  rewrite H2 in H.
  apply (Nat.lt_irrefl yl H).
Qed.

Lemma starts_not_precedes : forall x y, starts x y -> ~x < y.
Proof.
  unfold starts, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H1 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma starts_not_preceded : forall x y, starts x y -> ~x > y.
Proof.
  unfold starts, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H1 in q.
  rewrite H in q.
  apply (Nat.lt_irrefl yl q).
Qed.
Lemma starts_not_meets : forall x y, starts x y -> ~meets x y.
Proof.
  unfold starts, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma starts_not_met : forall x y, starts x y -> ~met x y.
Proof.
  unfold starts, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite <- H in q.
  rewrite <- H1 in q.
  apply (Nat.lt_irrefl yr q).
Qed.
Lemma starts_not_overlaps : forall x y, starts x y -> ~overlaps x y.
Proof.
  unfold starts, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma starts_not_overlapped : forall x y, starts x y -> ~overlapped x y.
Proof.
  unfold starts, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma starts_not_during : forall x y, starts x y -> ~during x y.
Proof.
  unfold starts, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma starts_not_contains : forall x y, starts x y -> ~contains x y.
Proof.
  unfold starts, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma starts_not_finishes : forall x y, starts x y -> ~finishes x y.
Proof.
  unfold starts, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H2 in H0.
  apply (Nat.lt_irrefl yr H0).
Qed.
Lemma starts_not_finished : forall x y, starts x y -> ~finished x y.
  unfold starts, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma starts_not_equal : forall x y, starts x y -> ~x == y.
  unfold starts, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H2 in H0.
  apply (Nat.lt_irrefl yr H0).
Qed.

Lemma during_not_precedes : forall x y, during x y -> ~x < y.
Proof.
  unfold during, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H1 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma during_not_preceded : forall x y, during x y -> ~x > y.
Proof.
  unfold during, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma during_not_meets : forall x y, during x y -> ~meets x y.
Proof.
  unfold during, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite <- H1 in H.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma during_not_met : forall x y, during x y -> ~met x y.
Proof.
  unfold during, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma during_not_overlaps : forall x y, during x y -> ~overlaps x y.
Proof.
  unfold during, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H in H1.
  apply (Nat.lt_irrefl xl H1).
Qed.
Lemma during_not_overlapped : forall x y, during x y -> ~overlapped x y.
Proof.
  unfold during, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H3 in H0.
  apply (Nat.lt_irrefl xr H0).
Qed.
Lemma during_not_starts : forall x y, during x y -> ~starts x y.
Proof.
  unfold during, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl yl H).
Qed.
Lemma during_not_started : forall x y, during x y -> ~started x y.
Proof.
  unfold during, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl xl H).
Qed.
Lemma during_not_finishes : forall x y, during x y -> ~finishes x y.
Proof.
  unfold during, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H2 in H0.
  apply (Nat.lt_irrefl yr H0).
Qed.
Lemma during_not_finished : forall x y, during x y -> ~finished x y.
  unfold during, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl xl H1).
Qed.
Lemma during_not_equal : forall x y, during x y -> ~x == y.
  unfold during, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H2 in H0.
  apply (Nat.lt_irrefl yr H0).
Qed.

Lemma finishes_not_precedes : forall x y, finishes x y -> ~x < y.
Proof.
  unfold finishes, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H1 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma finishes_not_preceded : forall x y, finishes x y -> ~x > y.
Proof.
  unfold finishes, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma finishes_not_meets : forall x y, finishes x y -> ~meets x y.
Proof.
  unfold finishes, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite <- H1 in H.
  rewrite H in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma finishes_not_met : forall x y, finishes x y -> ~met x y.
Proof.
  unfold finishes, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma finishes_not_overlaps : forall x y, finishes x y -> ~overlaps x y.
Proof.
  unfold finishes, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H in H1.
  apply (Nat.lt_irrefl xl H1).
Qed.
Lemma finishes_not_overlapped : forall x y, finishes x y -> ~overlapped x y.
Proof.
  unfold finishes, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H0 in H3.
  apply (Nat.lt_irrefl yr H3).
Qed.
Lemma finishes_not_starts : forall x y, finishes x y -> ~starts x y.
Proof.
  unfold finishes, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl yl H).
Qed.
Lemma finishes_not_started : forall x y, finishes x y -> ~started x y.
Proof.
  unfold finishes, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl xl H).
Qed.
Lemma finishes_not_during : forall x y, finishes x y -> ~during x y.
Proof.
  unfold finishes, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H0 in H2.
  apply (Nat.lt_irrefl yr H2).
Qed.
Lemma finishes_not_contains : forall x y, finishes x y -> ~contains x y.
  unfold finishes, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl xl H1).
Qed.
Lemma finishes_not_equal : forall x y, finishes x y -> ~x == y.
  unfold finishes, equal, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H1 in H.
  apply (Nat.lt_irrefl yl H).
Qed.

Lemma equal_not_precedes : forall x y, equal x y -> ~x < y.
Proof.
  unfold equal, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H1 in p.
  rewrite H in p.
  apply (Nat.lt_irrefl yl p).
Qed.
Lemma equal_not_preceded : forall x y, equal x y -> ~x > y.
Proof.
  unfold equal, precedes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma equal_not_meets : forall x y, equal x y -> ~meets x y.
Proof.
  unfold equal, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite <- H1 in H.
  rewrite H in p.
  apply (Nat.lt_irrefl xr p).
Qed.
Lemma equal_not_met : forall x y, equal x y -> ~met x y.
Proof.
  unfold equal, meets, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] H1.
  rewrite H0 in p.
  rewrite H1 in p.
  apply (Nat.lt_irrefl xl p).
Qed.
Lemma equal_not_overlaps : forall x y, equal x y -> ~overlaps x y.
Proof.
  unfold equal, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma equal_not_overlapped : forall x y, equal x y -> ~overlapped x y.
Proof.
  unfold equal, overlaps, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 [H2 H3]].
  rewrite H0 in H3.
  apply (Nat.lt_irrefl yr H3).
Qed.
Lemma equal_not_starts : forall x y, equal x y -> ~starts x y.
Proof.
  unfold equal, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H0 in H2.
  apply (Nat.lt_irrefl yr H2).
Qed.
Lemma equal_not_started : forall x y, equal x y -> ~started x y.
Proof.
  unfold equal, starts, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H0 in H2.
  apply (Nat.lt_irrefl yr H2).
Qed.
Lemma equal_not_during : forall x y, equal x y -> ~during x y.
Proof.
  unfold equal, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H0 in H2.
  apply (Nat.lt_irrefl yr H2).
Qed.
Lemma equal_not_contains : forall x y, equal x y -> ~contains x y.
  unfold equal, during, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma equal_not_finishes : forall x y, equal x y -> ~finishes x y.
Proof.
  unfold equal, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.
Lemma equal_not_finished : forall x y, equal x y -> ~finished x y.
  unfold equal, finishes, not.
  intros ((xl, xr), p) ((yl, yr), q). simpl in p, q. simpl.
  intros [H H0] [H1 H2].
  rewrite H in H1.
  apply (Nat.lt_irrefl yl H1).
Qed.

Theorem precedes_exclusivity : forall x y, x < y ->
  ~preceded x y /\ ~meets      x y /\ ~met      x y /\
  ~overlaps x y /\ ~overlapped x y /\ ~starts   x y /\ ~started  x y /\
  ~during   x y /\ ~contains   x y /\ ~finishes x y /\ ~finished x y /\
  ~equal    x y.
Proof.
  intros x y H.
  split. apply (precedes_asym x y H).
  split. apply (precedes_not_meets x y H).
  split. apply (precedes_not_met x y H).
  split. apply (precedes_not_overlaps x y H).
  split. apply (precedes_not_overlapped x y H).
  split. apply (precedes_not_starts x y H).
  split. apply (precedes_not_started x y H).
  split. apply (precedes_not_during x y H).
  split. apply (precedes_not_contains x y H).
  split. apply (precedes_not_finishes x y H).
  split. apply (precedes_not_finished x y H).
  apply (precedes_not_equal x y H).
Qed.
Theorem meets_exclusivity : forall x y, meets x y ->
  ~precedes x y /\ ~preceded   x y /\ ~met      x y /\
  ~overlaps x y /\ ~overlapped x y /\ ~starts   x y /\ ~started  x y /\
  ~during   x y /\ ~contains   x y /\ ~finishes x y /\ ~finished x y /\
  ~equal    x y.
Proof.
  intros x y H.
  split. apply (meets_not_precedes x y H).
  split. apply (meets_not_preceded x y H).
  split. apply (meets_asym x y H).
  split. apply (meets_not_overlaps x y H).
  split. apply (meets_not_overlapped x y H).
  split. apply (meets_not_starts x y H).
  split. apply (meets_not_started x y H).
  split. apply (meets_not_during x y H).
  split. apply (meets_not_contains x y H).
  split. apply (meets_not_finishes x y H).
  split. apply (meets_not_finished x y H).
  apply (meets_not_equal x y H).
Qed.
Theorem overlaps_exclusivity : forall x y, overlaps x y ->
  ~precedes   x y /\ ~preceded   x y /\ ~meets    x y /\ ~met      x y /\
  ~overlapped x y /\ ~starts     x y /\ ~started  x y /\
  ~during     x y /\ ~contains   x y /\ ~finishes x y /\ ~finished x y /\
  ~equal      x y.
Proof.
  intros x y H.
  split. apply (overlaps_not_precedes x y H).
  split. apply (overlaps_not_preceded x y H).
  split. apply (overlaps_not_meets x y H).
  split. apply (overlaps_not_met x y H).
  split. apply (overlaps_asym x y H).
  split. apply (overlaps_not_starts x y H).
  split. apply (overlaps_not_started x y H).
  split. apply (overlaps_not_during x y H).
  split. apply (overlaps_not_contains x y H).
  split. apply (overlaps_not_finishes x y H).
  split. apply (overlaps_not_finished x y H).
  apply (overlaps_not_equal x y H).
Qed.
Theorem starts_exclusivity : forall x y, starts x y ->
  ~precedes   x y /\ ~preceded   x y /\ ~meets    x y /\ ~met      x y /\
  ~overlaps   x y /\ ~overlapped x y /\ ~started  x y /\
  ~during     x y /\ ~contains   x y /\ ~finishes x y /\ ~finished x y /\
  ~equal      x y.
Proof.
  intros x y H.
  split. apply (starts_not_precedes x y H).
  split. apply (starts_not_preceded x y H).
  split. apply (starts_not_meets x y H).
  split. apply (starts_not_met x y H).
  split. apply (starts_not_overlaps x y H).
  split. apply (starts_not_overlapped x y H).
  split. apply (starts_asym x y H).
  split. apply (starts_not_during x y H).
  split. apply (starts_not_contains x y H).
  split. apply (starts_not_finishes x y H).
  split. apply (starts_not_finished x y H).
  apply (starts_not_equal x y H).
Qed.
Theorem during_exclusivity : forall x y, during x y ->
  ~precedes   x y /\ ~preceded   x y /\ ~meets    x y /\ ~met      x y /\
  ~overlaps   x y /\ ~overlapped x y /\ ~starts   x y /\ ~started  x y /\
  ~contains   x y /\ ~finishes   x y /\ ~finished x y /\
  ~equal      x y.
Proof.
  intros x y H.
  split. apply (during_not_precedes x y H).
  split. apply (during_not_preceded x y H).
  split. apply (during_not_meets x y H).
  split. apply (during_not_met x y H).
  split. apply (during_not_overlaps x y H).
  split. apply (during_not_overlapped x y H).
  split. apply (during_not_starts x y H).
  split. apply (during_not_started x y H).
  split. apply (during_asym x y H).
  split. apply (during_not_finishes x y H).
  split. apply (during_not_finished x y H).
  apply (during_not_equal x y H).
Qed.
Theorem finishes_exclusivity : forall x y, finishes x y ->
  ~precedes   x y /\ ~preceded   x y /\ ~meets    x y /\ ~met      x y /\
  ~overlaps   x y /\ ~overlapped x y /\ ~starts   x y /\ ~started  x y /\
  ~during     x y /\ ~contains   x y /\ ~finished x y /\
  ~equal      x y.
Proof.
  intros x y H.
  split. apply (finishes_not_precedes x y H).
  split. apply (finishes_not_preceded x y H).
  split. apply (finishes_not_meets x y H).
  split. apply (finishes_not_met x y H).
  split. apply (finishes_not_overlaps x y H).
  split. apply (finishes_not_overlapped x y H).
  split. apply (finishes_not_starts x y H).
  split. apply (finishes_not_started x y H).
  split. apply (finishes_not_during x y H).
  split. apply (finishes_not_contains x y H).
  split. apply (finishes_asym x y H).
  apply (finishes_not_equal x y H).
Qed.
Theorem equal_exclusivity : forall x y, equal x y ->
  ~precedes   x y /\ ~preceded   x y /\ ~meets    x y /\ ~met      x y /\
  ~overlaps   x y /\ ~overlapped x y /\ ~starts   x y /\ ~started  x y /\
  ~during     x y /\ ~contains   x y /\ ~finishes x y /\ ~finished x y.
Proof.
  intros x y H.
  split. apply (equal_not_precedes x y H).
  split. apply (equal_not_preceded x y H).
  split. apply (equal_not_meets x y H).
  split. apply (equal_not_met x y H).
  split. apply (equal_not_overlaps x y H).
  split. apply (equal_not_overlapped x y H).
  split. apply (equal_not_starts x y H).
  split. apply (equal_not_started x y H).
  split. apply (equal_not_during x y H).
  split. apply (equal_not_contains x y H).
  split. apply (equal_not_finishes x y H).
  apply (equal_not_finished x y H).
Qed.
Theorem preceded_exclusivity : forall x y, x > y ->
  ~precedes   x y /\ ~met      x y /\ ~meets     x y /\
  ~overlapped x y /\ ~overlaps x y /\ ~started   x y /\ ~starts   x y /\
  ~contains   x y /\ ~during   x y /\ ~finished  x y /\ ~finishes x y /\
  ~equal      x y.
intros x y. rewrite equal_sym_iff. apply (precedes_exclusivity y x). Qed.
Theorem met_exclusivity : forall x y, met x y ->
  ~preceded   x y /\ ~precedes x y /\ ~meets     x y /\
  ~overlapped x y /\ ~overlaps x y /\ ~started   x y /\ ~starts   x y /\
  ~contains   x y /\ ~during   x y /\ ~finished  x y /\ ~finishes x y /\
  ~equal      x y.
intros x y. rewrite equal_sym_iff. apply (meets_exclusivity y x). Qed.
Theorem overlapped_exclusivity : forall x y, overlapped x y ->
  ~preceded x y /\ ~precedes x y /\ ~met      x y /\ ~meets    x y /\
  ~overlaps x y /\ ~started  x y /\ ~starts   x y /\
  ~contains x y /\ ~during   x y /\ ~finished x y /\ ~finishes x y /\
  ~equal    x y.
intros x y. rewrite equal_sym_iff. apply (overlaps_exclusivity y x). Qed.
Theorem started_exclusivity : forall x y, started x y ->
  ~preceded   x y /\ ~precedes x y /\ ~met      x y /\ ~meets    x y /\
  ~overlapped x y /\ ~overlaps x y /\ ~starts   x y /\
  ~contains   x y /\ ~during   x y /\ ~finished x y /\ ~finishes x y /\
  ~equal      x y.
intros x y. rewrite equal_sym_iff. apply (starts_exclusivity y x). Qed.
Theorem contains_exclusivity : forall x y, contains x y ->
  ~preceded   x y /\ ~precedes x y /\ ~met      x y /\ ~meets    x y /\
  ~overlapped x y /\ ~overlaps x y /\ ~started  x y /\ ~starts   x y /\
  ~during     x y /\ ~finished x y /\ ~finishes x y /\
  ~equal      x y.
intros x y. rewrite equal_sym_iff. apply (during_exclusivity y x). Qed.
Theorem finished_exclusivity : forall x y, finished x y ->
  ~preceded   x y /\ ~precedes x y /\ ~met      x y /\ ~meets    x y /\
  ~overlapped x y /\ ~overlaps x y /\ ~started  x y /\ ~starts   x y /\
  ~contains   x y /\ ~during   x y /\ ~finishes x y /\
  ~equal      x y.
intros x y. rewrite equal_sym_iff. apply (finishes_exclusivity y x). Qed.




(*
Theorem rcc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { ntppi i j } + { eq i j } +
  { ntpp i j } + { tppileft i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
  unfold dcleft, ecleft, poleft, tppiright, tppleft,
         eq, ntppi, tppileft, ntpp, tppright, poright.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { do 12 left. assumption. }
  (* ecleft (ir = jl) *)
  { do 11 left. now right. }
  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr).
    destruct s, s0.
    (* poleft (il < jl /\ jl < ir < jr) *)
    { do 10 left. right. easy. }
    (* tppiright (il < jl /\ ir = jl) *)
    { do 9 left. right. easy. }
    (* tppleft (il = jl /\ ir < jr) *)
    { do 8 left. right. easy. }
    (* eq (il = jl /\ ir = jr) *)
    { do 6 left. right. easy. }
    { destruct s.
      (* ntppi (il < jl /\ jr < ir) *)
      { do 7 left. right. easy. }
      (* tppileft (jl = il /\ jr < ir) *)
      { do 4 left. right. easy. }
    }
    { destruct s.
      (* ntpp (jl < il /\ ir < jr) *)
      { do 5 left. right. easy. }
      (* tppright (jl < il /\ ir = jr) *)
      { do 3 left. right. easy. }
    }
    { destruct (lt_eq_lt_dec il jr). destruct s.
      (* poright (jl < il /\ il < jr < ir) *)
      { do 2 left. right. easy. }
      (* ecright (jr = il) *)
      { left. right. easy. }
      (* dcright (jr < il) *)
      { right. assumption. }
    }
  }
Qed.








(** disconnected left (precedes) *)
Definition dcleft   i j := right i <= left j.
(** partially overlapping left (overlaps) *)
Definition poleft   i j := left i < left j /\ left j + 1 <= right i < right j.
(** tangential proper part left (starts) *)
Definition tppleft  i j := left i = left j /\ right i < right j.
(** tangential proper part right (finishes) *)
Definition tppright i j := left j < left i /\ right i = right j.
(** non-tangential proper part (during) *)
Definition ntpp     i j := left j < left i /\ right i < right j.
(** equal (equal to) *)
Definition eq       i j := left i = left j /\ right i = right j.

(** disconnected right (preceded) *)
Notation dcright    i j := (dcleft j i)   (only parsing).
(** externally connected right (met) *)
Notation ecright    i j := (ecleft j i)   (only parsing).
(** partially overlapping left (overlaped) *)
Notation poright    i j := (poleft j i)   (only parsing).
(** tpp inverse left (started) *)
Notation tppileft   i j := (tppleft j i)  (only parsing).
(** tpp inverse right (finished) *)
Notation tppiright  i j := (tppright j i) (only parsing).
(** ntpp inverse (contains) *)
Notation ntppi      i j := (ntpp j i)     (only parsing).

(** overlap
 * See {dc_overlap_dec} and {overlap_dec}.
 *)
(*
overlap i j
  = ~dcleft i j /\ ~dcright i j
  = ~right i < left j /\ ~right j < left i
  = left j <= right i /\ left i <= right j
 *)
Definition overlap i j := left j <= right i /\ left i <= right j.
(** proper overlap
 * See {dc_ec_poverlap} and {poverlap_dec}.
 *)
(*
poverlap i j
  = overlap /\ ~ecleft i j /\ ~ecright i j
  = left j <= right i /\ left i <= right j /\ ~right i = left j /\ ~right j = left i
  = left j < right i /\ left i < right j
*)
Definition poverlap i j :=
  left j < right i /\ left i < right j.


(** Aliases *)
Notation lt     i j := (dcleft i j)  (only parsing).
Notation gt     i j := (dcleft j i) (only parsing).
Notation subset i j := (ntpp i j) (only parsing).
Notation supset i j := (ntpp j i) (only parsing).
(** `Isubseteq <> Isubset \/ Ieq` so subset is not defined. *)

(** Infix *)
Infix "==" := eq (at level 70, no associativity) : Interval_scope.
Infix "<" := dcleft : Interval_scope.
Notation "i > j" := (dcleft j i) (only parsing) : Interval_scope.
Notation "i < j < k" := (i<j /\ j<k) : Interval_scope.

Theorem eq_sym : forall i j, i == j -> j == i.
Proof.
  unfold eq. intros i j (H, H0). easy.
Qed.


(** ** Decidability *)

Lemma foo : forall i j, tppleft i j -> ~ ecright i j.
Proof.
  unfold tppleft, ecright.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros [H H0].
  apply (Nat.le_lt_trans il ir jr p) in H0.
  apply Nat. in H0.

Theorem eq_dec : forall i j, {i == j} + {~ i == j}.
Proof.
  unfold eq. destruct i as ((il, ir), p), j as ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (Nat.eq_dec il jl), (Nat.eq_dec ir jr).
  { left. easy. }
  { right. easy. }
  { right. easy. }
  { right. easy. }
Qed.

Theorem rcc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { ntppi i j } + { eq i j } +
  { ntpp i j } + { tppileft i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
Proof.
  unfold dcleft, ecleft, poleft, tppiright, tppleft,
         eq, ntppi, tppileft, ntpp, tppright, poright.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { do 12 left. assumption. }
  (* ecleft (ir = jl) *)
  { do 11 left. now right. }
  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr).
    destruct s, s0.
    (* poleft (il < jl /\ jl < ir < jr) *)
    { do 10 left. right. easy. }
    (* tppiright (il < jl /\ ir = jl) *)
    { do 9 left. right. easy. }
    (* tppleft (il = jl /\ ir < jr) *)
    { do 8 left. right. easy. }
    (* eq (il = jl /\ ir = jr) *)
    { do 6 left. right. easy. }
    { destruct s.
      (* ntppi (il < jl /\ jr < ir) *)
      { do 7 left. right. easy. }
      (* tppileft (jl = il /\ jr < ir) *)
      { do 4 left. right. easy. }
    }
    { destruct s.
      (* ntpp (jl < il /\ ir < jr) *)
      { do 5 left. right. easy. }
      (* tppright (jl < il /\ ir = jr) *)
      { do 3 left. right. easy. }
    }
    { destruct (lt_eq_lt_dec il jr). destruct s.
      (* poright (jl < il /\ il < jr < ir) *)
      { do 2 left. right. easy. }
      (* ecright (jr = il) *)
      { left. right. easy. }
      (* dcright (jr < il) *)
      { right. assumption. }
    }
  }
Qed.

(* jl < ir /\ il < jr. *)
(*
Lemma poleft_poverlap : forall i j, poleft i j -> poverlap i j.
  unfold poleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros [H [H0 H1]].
  split. assumption. apply (Nat.le_lt_trans il ir jr p H1).
Qed.
Lemma tppleft_poverlap : forall i j, tppleft i j -> poverlap i j.
  unfold tppleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros [H H0].
  split.
Lemma eq_poverlap : forall i j, eq i j -> poverlap i j.
  unfold poverlap. intros i j H. do 4 right. left. assumption. Qed.
Lemma ntpp_poverlap : forall i j, ntpp i j -> poverlap i j.
  unfold poverlap. intros i j H. do 5 right. left. assumption. Qed.
Lemma tppright_poverlap : forall i j, tppright i j -> poverlap i j.
  unfold poverlap. intros i j H. do 7 right. left. assumption. Qed.
 *)

Lemma ecleft_overlap : forall i j, ecleft i j -> overlap i j.
Proof.
  unfold ecleft, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intro H. split.
  { apply Nat.le_lteq. now right. }
  { rewrite H in p. apply (Nat.le_trans il jl jr p q). }
Qed.
Lemma poleft_overlap : forall i j, poleft i j -> overlap i j.
Proof.
  unfold poleft, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H [H0 H1]]. split.
  { apply Nat.lt_le_incl. assumption. }
  { apply Nat.lt_le_incl. apply (Nat.le_lt_trans il ir jr p H1). }
Qed.
Lemma tppleft_overlap : forall i j, tppleft i j -> overlap i j.
Proof.
  unfold tppleft, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H H0]. split.
  { rewrite H in p. assumption. }
  { rewrite <- H in q. assumption. }
Qed.
Lemma eq_overlap : forall i j, eq i j -> overlap i j.
Proof.
  unfold eq, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H H0]. split.
  { rewrite <- H0 in q. assumption. }
  { rewrite H0 in p. assumption. }
Qed.
Lemma ntpp_overlap : forall i j, ntpp i j -> overlap i j.
Proof.
  unfold ntpp, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H H0]. split.
  { apply Nat.lt_le_incl. apply (Nat.lt_le_trans jl il ir H p). }
  { apply Nat.lt_le_incl. apply (Nat.le_lt_trans il ir jr p H0). }
Qed.
Lemma tppright_overlap : forall i j, tppright i j -> overlap i j.
Proof.
  unfold tppright, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H H0]. split.
  { rewrite <- H0 in q. assumption. }
  { rewrite H0 in p. assumption. }
Qed.

Lemma poverlap_sym_iff : forall i j, poverlap i j <-> poverlap j i.
Proof. unfold poverlap. easy. Qed.

Lemma overlap_sym_iff : forall i j, overlap i j <-> overlap j i.
Proof. unfold overlap. easy. Qed.

Theorem dc_ec_poverlap_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poverlap i j } + { ecright i j } + { dcright i j }.
Proof.
  unfold dcleft, ecleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { do 4 left. assumption. }
  (* ecleft (ir = jl) *)
  { do 3 left. now right. }
  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr).
    destruct s, s0.
    (* poleft (il < jl /\ jl < ir < jr) *)
    { do 2 left; right. split.
      assumption. apply (Nat.le_lt_trans il ir jr p l1).
    }
    (* tppiright (il < jl /\ ir = jl) *)
    { do 2 left; right. split.
      assumption. apply (Nat.lt_le_trans il jl jr l0 q).
    }
    (* tppleft (il = jl /\ ir < jr) *)
    { do 2 left; right. split.
      assumption. apply (Nat.le_lt_trans il ir jr p l0).
    }
    (* eq (il = jl /\ ir = jr) *)
    { do 2 left; right. split.
      assumption. rewrite e0, <- e in l. assumption.
    }
    { destruct s.
      (* ntppi (il < jl /\ jr < ir) *)
      { do 2 left; right. split.
        assumption. apply (Nat.lt_le_trans il jl jr l1 q).
      }
      (* tppileft (jl = il /\ jr < ir) *)
      { do 2 left; right. split.
        assumption. apply ()
      }
    }
    { destruct s.
      (* ntpp (jl < il /\ ir < jr) *)
      { do 5 left. right. easy. }
      (* tppright (jl < il /\ ir = jr) *)
      { do 3 left. right. easy. }
    }
    { destruct (lt_eq_lt_dec il jr). destruct s.
      (* poright (jl < il /\ il < jr < ir) *)
      { do 2 left. right. easy. }
      (* ecright (jr = il) *)
      { left. right. easy. }
      (* dcright (jr < il) *)
      { right. assumption. }
    }
  }



  unfold dcleft, ecleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  { do 4 left. assumption. }
  { do 3 left; right. assumption. }
  { destruct (lt_eq_lt_dec il jl). destruct s.
    { do 2 left; right. split.
      { assumption. }
      { apply (Nat.lt_le_trans il jl jr l0 q). }
    }
    destruct (lt_eq_lt_dec jr il). destruct s.
    { right. assumption. }
    { left; right. assumption. }
    { do 2 left; right. split. assumption. assumption. }
    { destruct (lt_eq_lt_dec ir jr). destruct s.
      { do 2 left; right. split.
        { assumption. }
        { apply (Nat.le_lt_trans il ir jr p l1). }
      }
      { do 2 left; right. split.
        { assumption. }
        { rewrite e in p. assumption. }
      }
    }
  }

  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr). destruct s, s0.
    { do 2 left; right. split.
      { assumption. }
      { apply (Nat.le_lt_trans il ir jr p l1). }
    }
    { do 2 left. right. split.
      { assumption. }
      { rewrite e in p. }
    }
  }

  intros i j. destruct (rcc_dec i j). repeat destruct s.
  { do 4 left. assumption. }
  { do 3 left; right. assumption. }
  { do 2 left; right. apply (poleft_poverlap i j p). }
  { do 2 left; right. apply poverlap_sym_iff. apply (tppright_poverlap j i t). }
  { do 2 left; right. apply (tppleft_poverlap i j t). }
  { do 2 left; right. apply poverlap_sym_iff. apply (ntpp_poverlap j i n). }
  { do 2 left; right. apply (eq_poverlap i j e). }
  { do 2 left; right. apply (ntpp_poverlap i j n). }
  { do 2 left; right. apply poverlap_sym_iff. apply (tppleft_poverlap j i t). }
  { do 2 left; right. apply (tppright_poverlap i j t). }
  { do 2 left; right. apply poverlap_sym_iff. apply (poleft_poverlap j i p). }
  {      left; right. assumption. }
  {            right. assumption. }
Qed.

Theorem dc_overlap_dec : forall i j, { i < j } + { overlap i j } + { i > j }.
Proof.
  intros i j.
  destruct (rcc_dec i j). repeat destruct s.
  { do 2 left. assumption. }
  { left; right. apply (ecleft_overlap i j e). }
  { left; right. apply (poleft_overlap i j p). }
  { left; right. apply overlap_sym_iff. apply (tppright_overlap j i t). }
  { left; right. apply (tppleft_overlap i j t). }
  { left; right. apply overlap_sym_iff. apply (ntpp_overlap j i n). }
  { left; right. apply (eq_overlap i j e). }
  { left; right. apply (ntpp_overlap i j n). }
  { left; right. apply overlap_sym_iff. apply (tppleft_overlap j i t). }
  { left; right. apply (tppright_overlap i j t). }
  { left; right. apply overlap_sym_iff. apply (poleft_overlap j i p). }
  { left; right. apply overlap_sym_iff. apply (ecleft_overlap j i e). }
  { now right. }
Qed.

(*
Lemma poleft_overlap : forall i j, poleft i j -> overlap i j.
Lemma poverlap_overlap : forall i j, poverlap i j -> overlap i j.
*)
Lemma dcleft_not_poverlap : forall i j, dcleft i j -> ~poverlap i j.
Proof.
  unfold not, poverlap.
  intros i j H0 H1.

Theorem poverlap_dec : forall i j, poverlap i j ->
  { poleft i j } + { tppiright i j } + { tppleft i j } +
  { ntppi i j } + { eq i j } + { ntpp i j } +
  { tppileft i j } + { tppright i j } + { poright i j }.
Proof.
  intros i j H. destruct (rcc_dec i j). repeat destruct s.

  intros i j H. destruct (rcc_dec i j). repeat destruct s.
  { 
    unfold poverlap in H.
    unfold poverlap, poleft, tppright, tppleft, ntpp, eq in H. unfold dcleft in d.
    destruct i as ((il, ir), p). destruct j as ((jl, jr), q).
    simpl in H, d, p, q.
    destruct H as [ H | H2 ]. simpl.
destruct (i, j) as (((il, ir), p), ((jl, jr), q)).
    simpl in H.
  }
  3: {  }
  { unfold poverlap in H. }

(*
Lemma poverlap_not_dc : forall i j, poverlap i j -> ~i < j.
Proof.
  unfold poverlap, poleft, tppright, tppleft, ntpp, eq, dcleft, not.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros H H0. destruct H.
  { destruct H as [H [H1 H2]].
    apply (Nat.lt_trans jl ir jl H1) in H0.
    apply (Nat.lt_irrefl jl H0).
  }
  destruct H.
  { destruct H.
    rewrite H1 in q.
    apply (Nat.le_lt_trans jl ir jl q) in H0.
    apply (Nat.lt_irrefl jl H0).
  }
  destruct H. 
  { destruct H.
    apply (Nat.le_lt_trans il ir jl p) in H0.
    rewrite H in H0.
    apply (Nat.lt_irrefl jl H0).
  }
  destruct H.
Qed.
*)

Lemma overlap_not_lt : forall i j, overlap i j -> ~i < j.
Proof.
  unfold overlap, not, lt.
  intros ((il, ir), p) ((jl, jr), q) [H H0] H1.
  apply (Nat.le_lt_trans jl ir jl H) in H1.
  apply (Nat.lt_irrefl jl H1).
Qed.


Theorem overlap_dec : forall i j, overlap i j ->
  { ecleft i j } + { poleft i j } + { tppiright i j } + { tppleft i j } +
  { ntppi i j } + { eq i j } + { ntpp i j } +
  { tppileft i j } + { tppright i j } + { poright i j } + {ecright i j}.
Proof.
  intros i j H.
  destruct (rcc_dec i j). repeat destruct s.
  { apply (overlap_not_lt i j H) in d. contradiction. }
  { do 10 left. assumption. }
  { do 9 left; right. assumption. }
  { do 8 left; right. assumption. }
  { do 7 left; right. assumption. }
  { do 6 left; right. assumption. }
  { do 5 left; right. assumption. }
  { do 4 left; right. assumption. }
  { do 3 left; right. assumption. }
  { do 2 left; right. assumption. }
  { left; right. assumption. }
  { right. assumption. }
  { apply (overlap_sym_iff i j) in H.
    apply (overlap_not_lt j i H) in d.
    contradiction.
  }
Qed.


Lemma poverlap_overlap : forall i j, poverlap i j -> overlap i j.
Proof.
  unfold poverlap.
  intros i j H.


  apply (overlap_dec i j).
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H H0].
  split.
  { apply Nat.lt_le_incl. assumption. }
  { apply Nat.lt_le_incl. assumption. }
Qed.



Lemma ecleft_overlap : forall i j, ecleft i j -> overlap i j.






Theorem lt_overlap_lt_dec : forall i j, { i < j } + { overlap i j } + { i > j }.
Proof.
  intros i j.
  destruct (rcc_dec i j). repeat destruct s.
  { do 2 left. assumption. }
  { left. right. apply (ecleft_overlap i j e). }
  { left. right. apply (poleft_overlap i j p). }
  { left. right. apply overlap_sym_iff. apply (tppright_overlap j i t). }
  { left. right. apply (tppleft_overlap i j t). }
  { left. right. apply overlap_sym_iff. apply (ntpp_overlap j i n). }
  { left. right. apply (eq_overlap i j e). }
  { left. right. apply (ntpp_overlap i j n). }
  { left. right. apply overlap_sym_iff. apply (tppleft_overlap j i t). }
  { left. right. apply (tppright_overlap i j t). }
  { left. right. apply overlap_sym_iff. apply (poleft_overlap j i p). }
  { left. right. apply overlap_sym_iff. apply (ecleft_overlap j i e). }
  { now right. }
Qed.


Lemma poleft_poverlap : forall i j, poleft i j -> poverlap i j.
Proof.
  unfold poleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros [H [H0 H1]].
  split.
  { assumption. }
  { apply (Nat.le_lt_trans il ir jr p H1). }
Qed.
Lemma poleft_overlap_t : forall i j, poleft i j -> overlap i j.
  intros i j H.
  apply (poleft_poverlap i j) in H.
  apply (poverlap_overlap i j H).

Theorem overlap_ec_poverlap_dec : forall i j, overlap i j ->
  { ecleft i j } + { poverlap i j } + { ecright i j }.
Proof.
  intros i j H.
  destruct (rcc_dec i j). repeat destruct s.
  { apply (overlap_not_lt i j H) in d. contradiction. }
  { do 2 left. assumption. }
  { apply (poverlap_overlap i j) in H. }

Theorem lt_ec_poverlap_dec : forall i j,
  { i < j } + { ecleft i j } + { poverlap i j } + { ecright i j } + { i > j }.
Proof.
  intros i j.
  destruct (rcc_dec i j). repeat destruct s.
  { do 4 left. assumption. }
  { do 3 left. right. assumption. }
  {  }



Lemma ecleft_poverlap : forall i j, ecleft i j -> poverlap i j.
Lemma

Lemma overlap_ec_po_tpp_ntpp_eq : forall i j, overlap i j <->
  ecleft i j \/ poleft i j \/ tppiright i j \/ tppleft i j \/
  ntppi i j \/ eq i j \/ ntpp i j \/
  tppileft i j \/ tppright i j \/ poright i j \/ ecright i j.
Proof.
  intros i j.
  destruct (overlap_dec i j).

Theorem dc_ec_poverlap_dec : forall i j,
  {dcleft i j} + {ecleft i j} + {poverlap i j} + {ecright i j} + {dcright i j}.
Proof.
  unfold dcleft, ecleft, poverlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { do 4 left. assumption. }
  (* ecleft (ir = jl) *)
  { do 3 left. now right. }
  { destruct (lt_eq_lt_dec jr il). destruct s.
    (* dcright (jr < il) *)
    { now right. }
    (* ecright (jr = il) *)
    { left. now right. }
    (* poverlap (jl < ir /\ il < jr) *)
    { do 2 left. right. easy. }
  }
Qed.

Theorem lt_overlap_lt_dec : forall i j, {i < j} + {overlap i j} + {j < i}.
Proof.
  intros i j.
  destruct (rcc_dec i j). repeat destruct s.
  { do 2 left. assumption. }
  { left. right.
    unfold ecleft in e.
  }
  unfold lt, overlap.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  { do 2 left. assumption. }
  2: { left. right. split.
       { apply (Nat.lt_le_incl jl ir l). }
       { destruct (lt_eq_lt_dec ir jl). destruct s.
         {  }
       }
     }
  { destruct (lt_eq_lt_dec jr il). destruct s.
    { right. assumption. }
    { left. right. split.
      { rewrite e0 in q. apply (Nat.le_trans jl il ir q p). }
      { rewrite e in p. apply (Nat.le_trans il jl jr p q). }
    }
    { right. }
  }


Theorem poverlap_dec : forall i j, poverlap i j ->
  { poleft i j } + { tppiright i j } + { tppleft i j } +
  { ntppi i j } + { eq i j } + { ntpp i j } +
  { tppileft i j } + { tppright i j } + { poright i j }.
Proof.
  unfold poverlap, poleft, tppleft, eq, ntpp, tppright.
  intros ((il, ir), p) ((jl, jr), q).
  simpl in p, q. simpl.
  intros (H, H0). destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { apply (Nat.lt_trans jl ir jl H) in l.
    apply Nat.lt_irrefl in l.
    contradiction. }
  (* ecleft (ir = jl) *)
  { rewrite e in H. apply Nat.lt_irrefl in H. contradiction. }
  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr).
    destruct s, s0.
    (* poleft (il < jl /\ jl < ir /\ ir < jr) *)
    { do 8 left. easy. }
    (* tppiright (il < jl /\ ir = jl) *)
    { do 7 left. right. easy. }
    (* tppleft (il = jl /\ ir < jr) *)
    { do 6 left. right. easy. }
    (* eq (il = jl /\ ir = jr) *)
    { do 4 left. right. easy. }
    { destruct s. 
      (* ntppi (il < jl /\ jr < ir) *)
      { do 5 left. right. easy. }
      (* tppileft (jl = il /\ jr < ir) *)
      { do 2 left. right. easy. }
    }
    { destruct s.
      (* ntpp (jl < il /\ ir < jr) *)
      { do 3 left. right. easy. }
      (* tppright (jl < il /\ ir = jr) *)
      { left. right. easy. }
    }
    { right. easy. }
  }
Qed.

Theorem overlap_poverlap_dec : forall i j, overlap i j -> {ecleft i j} + {poverlap i j} + {ecright i j}.
Proof.
  unfold overlap, ecleft, overlap.
  intros i j H. destruct (poverlap_dec i j).
  {  }


Lemma overlap_ec_po_tpp_ntpp_eq : forall i j, overlap i j <->
  ecleft i j \/ poleft i j \/ tppiright i j \/ tppleft i j \/
  ntppi i j \/ eq i j \/ ntpp i j \/
  tppileft i j \/ tppright i j \/ poright i j \/ ecright i j.



Theorem rcc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { ntppi i j } + { eq i j } +
  { ntpp i j } + { tppileft i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
Proof.
  intros i j. destruct (dc_ec_overlap_dec i j). repeat destruct s.
  { do 12 left. assumption. }
  { do 11 left. now right. }
  { destruct (overlap_dec i j o). repeat destruct s.
    { do 10 left. now right. }
    { do 9 left. now right. }
    { do 8 left. now right. }
    { do 7 left. now right. }
    { do 6 left. now right. }
    { do 5 left. now right. }
    { do 4 left. now right. }
    { do 3 left. now right. }
    { do 2 left. now right. }
  }
  { left. now right. }
  { now right. }
Qed.



(** ** Operators *)

Definition intersection (i j : Interval) : Interval + unit.
  destruct (dc_ec_overlap_dec i j). repeat destruct s.
  (* dcleft i j *)
  1: { right. exact tt. }
  (* ecleft i j *)
  1: { right. exact tt. }
  (* ecright i j *)
  2: { right. exact tt. }
  (* dcright i j *)
  2: { right. exact tt. }
  (* poverlap i j *)
     { left.
       unfold overlap in o.
       destruct i as ((il, ir), p), j as ((jl, jr), q).
       simpl in p, q, o. destruct o.
       assert (max il jl < min ir jr)%nat.
       rewrite Nat.max_lub_lt_iff, Nat.min_glb_lt_iff, Nat.min_glb_lt_iff.
       easy.
       exact (exist _ (max il jl, min ir jr) H1).
     }
Defined.



(** ** Properties of basic relations *)

(*
refl
sym
sym_iff
trans
irrefl
asym
antisym

comm
*)









Definition Ieq i j := lb i = lb j /\ ub i = ub j.
Definition Ilt i j := ub i < lb j.
Notation Igt i j := (Ilt j i) (only parsing).

(* `Isubseteq <> Isubset \/ Ieq` so subset is not defined. *)
Definition Isubseteq i j := lb j <= lb i /\ ub i <= ub j.
Notation Isupseteq i j := (Isubseteq j i) (only parsing).

Definition Ioverlap (i j : Interval) : Prop :=
  (lb j <= ub i)%nat /\ (lb i <= ub j)%nat.

Definition Iintersection (i j : Interval) : Ioverlap i j -> Interval.
  unfold Ioverlap.
  destruct i as ((il, ir), p), j as ((jl, jr), q). simpl in p, q. simpl.
  intros (Hjl_le_ir, Hil_le_jr).
  assert (max il jl <= min ir jr)%nat.
  rewrite Nat.max_lub_iff, Nat.min_glb_iff, Nat.min_glb_iff.
  repeat split. assumption. assumption. assumption. assumption.
  exact (exist _ (max il jl, min ir jr) H).
Defined.

Infix "==" := Ieq (at level 70, no associativity) : Interval_scope.
Infix "<" := Ilt : Interval_scope.
Notation "x > y" := (Ilt y x)(only parsing) : Interval_scope.
Notation "x < y < z" := (x<y/\y<z) : Interval_scope.

#[global]
Hint Unfold Ieq Ilt Isubseteq Ioverlap Iintersection : iarith.
#[global]
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.


(** * Decidability *)

Theorem Ieq_dec : forall i j, {i == j} + {~ i == j}.
Proof.
  unfold Ieq. destruct i as ((il, ir), p), j as ((jl, jr), q). simpl in p, q. simpl.
  destruct (Nat.eq_dec il jl), (Nat.eq_dec ir jr).
  - left. split. assumption. assumption.
  - right. intros (H, H0). apply (n H0).
  - right. intros (H, H0). apply (n H).
  - right. intros (H, H0). apply (n H).
Qed.

Theorem Ilt_overlap_gt_dec : forall i j, {i < j} + {Ioverlap i j} + {i > j}.
Proof.
  unfold Ilt, Ioverlap.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  destruct (lt_eq_lt_dec ir jl). destruct s.
  - now left; left.
  - left. right. split.
    apply Nat.lt_eq_cases. now right.
    rewrite e in p.
    apply (Nat.le_trans il jl jr p q).
  - destruct (lt_eq_lt_dec jr il). destruct s.
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
Notation Ile i j := (ecleft i j \/ dcleft i j) (only parsing).
Notation Ige i j := (Ile j i) (only parsing).
Infix "<=" := Ile : Interval_scope.
Notation "i >= j" := (Ige i j)(only parsing) : Interval_scope.
Notation "i <= j <= k" := (i <= j /\ j <= k) : Interval_scope.

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
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros (H, H0). destruct (lt_eq_lt_dec ir jl). destruct s.
  (* dcleft (ir < jl) *)
  { apply (Nat.le_lt_trans jl ir jl H) in l. apply Nat.lt_irrefl in l. contradiction. }
  (* ecleft (ir = jl) *)
  { now left; left; left; left; left; left; left; left; left; left. }
  { destruct (lt_eq_lt_dec il jl), (lt_eq_lt_dec ir jr). destruct s, s0.
    (* poleft (il < jl /\ jl < ir /\ ir < jr) *)
    { left; left; left; left; left; left; left; left; left. right. 
       repeat split. assumption. assumption. assumption. }
    (* tppiright (il < jl /\ ir = jl) *)
    { left; left; left; left; left; left; left; left; right.
       split. assumption. now apply eq_sym. }
    (* tppleft (il = jl /\ ir < jr) *)
    { left; left; left; left; left; left; left; right.
       split. assumption. assumption. }
    (* eq (il = jl /\ ir = jr) *)
    { left; left; left; left; left; left; right.
       split. assumption. assumption. }
    { destruct s. 
      (* ntppi (il < jl /\ jr < ir) *)
      { left; left; left; left; left; right.
          split. assumption. assumption. }
      (* tppileft (jl = il /\ jr < ir) *)
      { left; left; left; left; right.
          split. now apply eq_sym. assumption. }
    }
    { destruct s.
      (* ntpp (jl < il /\ ir < jr) *)
      { left; left; left; right.
          split. assumption. assumption. }
      (* tppright (jl < il /\ ir = jr) *)
      { left; left; right.
          split. assumption. assumption. }
    }
    { destruct (lt_eq_lt_dec il jr). destruct s.
      (* poright (jl < il < jr < ir) *)
      { left; right.
          repeat split. assumption. assumption. assumption. }
      (* ecright (jl = ir) *)
      { right. now apply eq_sym. }
      (* dcright (il < jr) *)
      { apply (Nat.le_lt_trans il jr il H0) in l2.
        apply Nat.lt_irrefl in l2.
        contradiction. }
    }
  }
Qed.

(** Decidability of Relation Connection Calculus *)

Theorem rcc_dec : forall i j,
  { dcleft i j } + { ecleft i j } + { poleft i j } +
  { tppiright i j } + { tppleft i j } + { eq i j } + { ntppi i j } +
  { tppileft i j } + { ntpp i j } + { tppright i j } +
  { poright i j } + { ecright i j } + { dcright i j }.
Proof.
  intros i j. destruct (Ilt_overlap_gt_dec i j). destruct s.
  1: { now repeat left. }
  2: { now right. }
     { destruct (Ioverlap_dec i j i0). repeat destruct s.
       - do 11 left. now right.
       - do 10 left. now right.
       - do 9 left. now right.
       - do 8 left. now right.
       - do 7 left. now right.
       - do 6 left. now right.
       - do 5 left. now right.
       - do 4 left. now right.
       - do 3 left. now right.
       - do 2 left. now right.
       - do 1 left. now right.
     }
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

Theorem Inot_eq_sym i j : ~ i == j -> ~ j == i.
Proof.
  unfold Ieq, not. destruct i as ((il, ir), p), j as ((jl, jr), q). simpl in p, q. simpl.
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
  unfold Ile, Ieq. intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros Hir_le_jl Hjr_le_il. split.
  - apply (le_trans il ir jl p) in Hir_le_jl as Hil_le_jl.
    apply (le_trans jl jr il q) in Hjr_le_il as Hjl_le_il.
    apply (le_antisym il jl Hil_le_jl Hjl_le_il).
  - apply (le_trans ir jl jr Hir_le_jl) in q as Hir_le_jr.
    apply (le_trans jr il ir Hjr_le_il) in p as Hjr_le_ir.
    apply (le_antisym ir jr Hir_le_jr Hjr_le_ir).
Qed.

Lemma Ile_trans : forall i j k, i <= j -> j <= k -> i <= k.
Proof.
  unfold Ile. intros ((il, ir), p) ((jl, jr), q) ((lbk, ubk), r).
  simpl in p, q, r. simpl. intros Hir_le_jl Hjr_le_lbk.
  apply (le_trans ir jl jr Hir_le_jl) in q as Hir_le_jr.
  apply (le_trans ir jr lbk Hir_le_jr Hjr_le_lbk).
Qed.

Lemma Isubseteq_refl : forall i, Isubseteq i i.
Proof.
  unfold Isubseteq. split. apply le_refl. apply le_refl.
Qed.

Lemma Isubseteq_antisym : forall i j, Isubseteq i j -> Isubseteq j i -> i == j.
Proof.
  unfold Isubseteq, Ieq.
  intros i j (Hjl_le_il, Hir_le_jr) (Hil_le_jl, Hjr_le_ir). split.
  apply (le_antisym (lb i) (lb j) Hil_le_jl Hjl_le_il).
  apply (le_antisym (ub i) (ub j) Hir_le_jr Hjr_le_ir).
Qed.

Lemma Isubseteq_trans : forall i j k, Isubseteq i j -> Isubseteq j k -> Isubseteq i k.
Proof.
  unfold Isubseteq.
  intros i j k (Hjl_le_il, Hir_le_jr) (Hlbk_le_jl, Hjr_le_ubk). split.
  apply (le_trans (lb k) (lb j) (lb i) Hlbk_le_jl Hjl_le_il).
  apply (le_trans (ub i) (ub j) (ub k) Hir_le_jr Hjr_le_ubk).
Qed.

Lemma Ioverlap_refl : forall i, Ioverlap i i.
Proof.
  unfold Ioverlap. intros ((il, ir), p). simpl in p. simpl.
  split. assumption. assumption.
Qed.


Lemma Isubseteq_overlap :
  forall i j, Isubseteq i j -> Ioverlap i j.
Proof.
  unfold Isubset, Ioverlap.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros [(Hjl_lt_il, Hir_le_jr) | (Hjl_le_il, Hir_lt_jr)].
  - split.
    apply Nat.lt_eq_cases. left. now apply (lt_le_trans jl il ir).
    now apply (le_trans il ir jr).
  - split.
    now apply (le_trans jl il ir).
    apply Nat.lt_eq_cases. left. now apply (le_lt_trans il ir jr).
Qed.

Lemma Isupseteq_overlap :
  forall i j, Isupseteq i j -> Ioverlap i j.
Proof.
  intros. apply Ioverlap_sym. now apply Isubset_overlap.
Qed.

Lemma Iintersection_comm : forall i j (Hioj : Ioverlap i j) (Hjoi : Ioverlap j i),
  Iintersection i j Hioj == Iintersection j i Hjoi.
Proof.
  unfold Iintersection, Ieq, Ioverlap.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros (Hjl_le_ir, Hil_le_jr) (H, H0).
  simpl. split.
  apply Nat.max_comm. apply Nat.min_comm.
Qed.

Lemma Isubseteq_intersection : forall i j (Hioj : Ioverlap i j),
  Isubseteq (Iintersection i j Hioj) i /\ Isubseteq (Iintersection i j Hioj) j.
Proof.
  unfold Iintersection, Ieq, Ioverlap, Isubseteq.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros (Hjl_le_ir, Hil_le_jr). simpl. repeat split.
  - rewrite Nat.max_le_iff. left. apply le_refl.
  - rewrite Nat.min_le_iff. left. apply le_refl.
  - rewrite Nat.max_le_iff. right. apply le_refl.
  - rewrite Nat.min_le_iff. right. apply le_refl.
Qed.

Lemma Isubseteq_intersection_l : forall i j (Hioj : Ioverlap i j),
  Isubseteq i j -> Iintersection i j Hioj == i.
Proof.
  unfold Isubset, Iintersection, Ieq.
  intros ((il, ir), p) ((jl, jr), q). simpl in p, q. simpl.
  intros (Hjl_le_ir, Hil_le_jr) Hisjr. simpl in Hjl_le_ir, Hil_le_jr. simpl.
  rewrite Nat.max_l_iff, Nat.min_l_iff.
  destruct Hisjr as [(Hjl_lt_il, Hir_le_jr) | (jl_le_il, ir_lt_jr)].
  - split. now apply lt_le_weak. assumption.
  - split. assumption. now apply lt_le_weak.
Qed.

Lemma Isupseteq_intersection_r : forall i j (Hioj : Ioverlap i j),
  Isupseteq i j -> Iintersection i j Hioj == j.
Proof.
  intros.
  apply Ioverlap_sym in Hioj as Hjoi.
  assert (Iintersection i j Hioj == Iintersection j i Hjoi) as Hiij_eq_jii.
  apply (Iintersection_comm i j Hioj Hjoi).
  apply (Ieq_trans (Iintersection i j Hioj) (Iintersection j i Hjoi) j Hiij_eq_jii).
  now apply Isubset_intersection_l.
Qed.



(* ??? *)
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
