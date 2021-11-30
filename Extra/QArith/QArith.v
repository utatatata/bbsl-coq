Require Import Coq.QArith.QArith QOrderedType.

(** * Equality **)

Lemma Qeq_comm : forall x y, x == y <-> y == x.
Proof.
  split. now intro; apply Qeq_sym. now intro; apply Qeq_sym.
Qed.

(** * Comparison **)

Lemma Qlt_asym : forall x y, ~(x < y /\ y < x).
Proof.
  unfold not. intros x y (Hxlty, Hyltx). 
  q_order.
Qed.

(** To use rewrite, iff version is necessary. **)

Lemma Qlt_not_le_iff : forall x y, x < y <-> ~y <= x.
Proof.
  intros x y.
  apply (conj (Qlt_not_le x y) (Qnot_le_lt y x)).
Qed.

(** To use rewrite, iff version is necessary. **)

Lemma Qle_not_lt_iff : forall x y, x <= y <-> ~y < x.
Proof.
  intros x y.
  apply (conj (Qle_not_lt x y) (Qnot_lt_le y x)).
Qed.
