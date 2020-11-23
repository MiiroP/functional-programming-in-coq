Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (not Q -> not P).
Proof.
  intros P Q H. unfold not.
  intros G HP. apply H in HP. apply G in HP. apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  not (P /\ not P).
Proof.
  intros. unfold not. intros [HP HnP].
  apply HnP. apply HP.
Qed.

Lemma dist : forall P Q R : Prop,
  P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R [HP [HQ | HR]].
  - left. split.
    + apply HP.
    + apply HQ.
  - right. split.
    + apply HP.
    + apply HR.
Qed.

Lemma dist' : forall P Q R : Prop,
  (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
Proof.
  intros P Q R [[HP HQ] | [HP HR]].
  - split.
    + apply HP.
    + left. apply HQ.
  - split.
    + apply HP.
    + right. apply HR.
Qed.
