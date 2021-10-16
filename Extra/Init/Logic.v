Lemma nor_nandn : forall A B, ~(A \/ B) -> ~A /\ ~B.
Proof.
  unfold not. intros A B H. split.
  - intro. destruct H. now apply or_introl.
  - intro. destruct H. now apply or_intror.
Qed.
