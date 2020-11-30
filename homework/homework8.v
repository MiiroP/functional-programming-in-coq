From LF Require Export Logic.

Theorem or_distributes_over_and : forall P Q R: Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split. apply HQ. apply HR.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros. split.
    + intros. right. simpl in H. apply H.
    + intros [constra | H].
      * simpl in constra. destruct constra.
      * simpl. apply H.
  - intros l'' a. simpl. split.
    + intros [Heq | H].
      * left. left. apply Heq.
      * rewrite <- or_assoc. right.
        apply IH. apply H.
    + rewrite <- or_assoc. intros [Heq | H].
      * left. apply Heq.
      * right. apply IH. apply H.
Qed.

Theorem orb_true_iff : forall b1 b2,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [H1 | H2].
    + rewrite H1. simpl. reflexivity.
    + destruct b1.
      * simpl. reflexivity.
      * simpl. apply H2.
Qed.

Search excluded_middle.

Theorem not_exists_dist :
  excluded_middle -> forall (X: Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. intros Hem X P H x.
  unfold not in Hem. unfold not in H.
  assert (HPx : P x \/ (P x -> False)).
  { apply Hem. }
  destruct HPx as [HT | HF].
  - apply HT.
  - destruct H. exists x. apply HF.
Qed.


