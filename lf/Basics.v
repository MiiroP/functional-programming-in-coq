Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true
| false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition xorb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => false
            | false => true
            end
  | false => match b2 with
             | true => true
             | false => false
             end
  end.

Compute (xorb true true).

Compute (xorb false true).

Compute (xorb false false).

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition orb2 (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "! x" := (negb x) (at level 35).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Definition nandb' (b1:bool) (b2:bool) :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, _ => true
  end.

Definition nandb'' (b1:bool) (b2:bool) :=
  ! (b1 && b2).

Compute nandb'' true false.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_nandb'1: (nandb' true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb'2: (nandb' false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb'3: (nandb' false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb'4: (nandb' true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Definition andb3' (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Definition andb3'' (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (andb b1 b2) with
  | true => b3
  | false => false
  end.

Example test_andb3''1: (andb3'' true true true) = true.
Proof. simpl.
       reflexivity.
Qed.

Check true.

Check negb.

Check andb true.

Inductive rgb : Type :=
| red
| green
| blue.

Inductive color : Type :=
| black
| white
| primary (p : rgb).

Check primary.

Check (primary red).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
| B0
| B1.

Inductive nybble : Type :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

Module NatPlayground.
  Inductive nat : Type :=
  | O
  | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minusTwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minusTwo 4).

Check S : nat -> nat.

Check pred : nat -> nat.

Check minusTwo : nat -> nat.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Fixpoint div3_n (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S O) => false
  | S (S (S n')) => div3_n n'
  end.

Compute div3_n 0.
Compute div3_n 1.
Compute div3_n 2.
Compute div3_n 3.
Compute div3_n 999.

Example test_odd1: oddb 1 = true.
Proof. simpl.
       reflexivity.
Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Compute (plus 3 2).

  Fixpoint mult (n : nat) (m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute (exp 2 10).

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Compute factorial 8.

Compute factorial 5.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint eqb' (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S n', S m' => eqb' n' m'
  end.

Compute eqb' 3 6.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Fixpoint leb' (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => true
  | S n', S m' => leb' n' m'
  end.

Compute leb' 2 3.
Compute leb' 2 2.
Compute leb' 3 2.

Fixpoint lb (n m : nat) : bool :=
  match n, m with
  | _, O => false
  | O, S _ => true
  | S n', S m' => lb n' m'
  end.

Compute lb 2 3.
Compute lb 2 2.
Compute lb 3 2.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m: nat) : bool :=
  andb (leb n m) (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_o_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_practice : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros m n o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall n m : nat,
    (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem mult_n_1 : forall n : nat,
    n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
  - reflexivity.
  - destruct b.
    + simpl in H. discriminate.
    + simpl in H. discriminate.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint ack (m : nat) (n : nat) : nat :=
  match m with
  | O => S n
  | S m' => let fix ackn (n : nat) :=
              match n with
              | O => ack m' 1
              | S n' => ack m' (ackn n')
              end
            in ackn n
  end.

Compute ack 3 4.
(*
Fixpoint ackermann (m : nat) (n : nat) : nat :=
  match m with
  | O => S n
  | S m' => match n with
            | O => ackermann m' (S O)
            | S n' => ackermann m' (ackermann m n')
            end
  end.
*)

Fixpoint square (n : nat) : nat :=
  match n with
  | O => O
  | S n' => (square n') + 2 * n' + 1
  end.

Compute square 5.

Definition sqplus1 (n : nat) : nat :=
  let fix square' (n : nat) : nat :=
    match n with
    | O => O
    | S n' => (square n') + 2 * n' + 1
    end
  in square' n + 1.

Compute sqplus1 5.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - simpl. reflexivity.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. reflexivity.
Qed.

Inductive bin : Type :=
| Z
| A (n : bin)
| B (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B Z
  | A m' => B m'
  | B m' => A (incr m')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | A m' => mult (S (S O)) (bin_to_nat m')
  | B m' => plus (S O) (mult (S (S O)) (bin_to_nat m'))
  end.

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
