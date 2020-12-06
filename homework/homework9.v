Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.

Inductive div4 : nat -> Prop :=
| div4_0 : div4 0
| div4_SSSS (n : nat) (H : div4 n) : div4 (S (S (S (S n)))).

Example ex1 : div4 0.
Proof. apply div4_0. Qed.

Example ex2 : div4 8.
Proof.
  apply div4_SSSS. apply div4_SSSS. apply div4_0.
Qed.

Inductive divisible : nat -> nat -> Prop :=
| divisible_0 (m : nat) : divisible 0 m
| divisible_plus_m (n : nat) (m : nat) (H : divisible n m) : divisible (plus n m) m.

Example exd1 : divisible 0 5.
Proof. apply (divisible_0 5). Qed.

Example exd2 : divisible 21 7.
Proof.
  apply (divisible_plus_m 14). apply (divisible_plus_m 7). apply (divisible_plus_m 0).
  apply (divisible_0 7).
Qed.
