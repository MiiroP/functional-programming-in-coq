Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Enm En. induction En.
  - simpl in Enm. apply Enm.
  - apply IHEn. simpl in Enm. inversion Enm. apply H0.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Lnm. induction Lnm as [| m' Lnm' IHLmn'].
  - apply le_n.
  - apply le_S. apply IHLmn'.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m LS. inversion LS.
  - apply le_n.
  - apply le_trans with (n := (S n)).
    + apply le_S. apply le_n.
    + apply H0.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Lmn Lno. induction Lno as [| o' Lno' IHLno'].
  - apply Lmn.
  - apply le_S. apply IHLno'.
Qed.

Lemma le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b as [| b' IHb'].
  - rewrite <- plus_n_O. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m LE. split.
  - apply le_trans with (n := n1 + n2).
    + apply le_plus_l.
    + apply LE.
  - apply le_trans with (n := n2 + n1).
    + apply le_plus_l.
    + rewrite plus_comm. apply LE.
Qed.
