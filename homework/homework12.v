Set Warnings "-notation-overridden,-parsing".
From LF Require Export Rel.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros. inversion H.
  - apply le_n.
  - apply le_trans with (S n).
    + apply le_S. apply le_n.
    + apply H1.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros n.
  induction n as [| n'].
  - intros. inversion H.
  - intros. apply IHn'.
    apply le_S_n. apply H.
Qed.

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros.
  assert (Nonsense: 1 <= 0). {
    apply H. apply le_S. apply le_n.
  }
  inversion Nonsense.
Qed.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric. intros a.
  induction a as [| a'].
  - intros. inversion H0. reflexivity.
  - intros b Hab Hba. inversion Hab as [m | m H1 H2].
    + reflexivity.
    + apply f_equal. apply IHa'.
      * apply le_S_n. rewrite -> H2. apply Hab.
      * apply le_S_n. rewrite -> H2. apply Hba.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z Cxy. generalize dependent z.
  induction Cxy as [| x y' y Hxy' Cy'y IH].
  - intros. apply H.
  - intros z Cyz. apply (rt1n_trans R x y' z).
    + apply Hxy'.
    + apply IH. apply Cyz.
Qed.

