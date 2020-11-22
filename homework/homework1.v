(*Define the square function. *)

Fixpoint square (n : nat) : nat :=
  match n with
  | O => O
  | S n => plus (square n) (plus (mult (S (S O)) n) (S O))
  end.

Example test_square1 : square 5 = 25.

Proof. reflexivity. Qed.
Example test_square2 : square 15 = 225.

Proof. reflexivity. Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  - reflexivity.
  - destruct b.
    + discriminate.
    + discriminate.
Qed.


Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b.
  - simpl in H.
    rewrite -> H.
    reflexivity.
  - simpl in H.
    rewrite <- H.
    reflexivity.
Qed.
