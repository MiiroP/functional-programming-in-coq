From LF Require Export Maps.
From Coq Require Import Logic.FunctionalExtensionality.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  unfold t_update. apply functional_extensionality. intros x'.
  destruct (eqb_string x x').
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x; m) = m.
Proof.
  intros A m x. unfold t_update.
  apply functional_extensionality. intros x'.
  destruct (eqb_string x x') eqn:E.
  - rewrite eqb_string_true_iff in E.
    rewrite E. reflexivity.
  - reflexivity.
Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (HPQ : P /\ Q) (HQR : Q /\ R) =>
    match HPQ with
    | conj HP _ =>
      match HQR with
      | conj _ HR => conj HP HR
      end
    end.

