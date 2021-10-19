(** a part of De Morgan's laws **)

Lemma nor_nandn_iff : forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  intros A B. split.
  - intro HNAorB. split.
  -- intro HA. destruct HNAorB. now apply or_introl.
  -- intro HA. destruct HNAorB. now apply or_intror.
  - intros (HNA, HNB) [HA|HB]. apply (HNA HA). apply (HNB HB).
Qed.
