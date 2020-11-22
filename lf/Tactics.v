From LF Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
  intros n m o p e1 e2.
  rewrite <- e1. apply e2.
Qed.

Theorem silly_ex :
  (forall n : nat, evenb n = true -> oddb (S n) = true) ->
  evenb 2 = true -> oddb 3 = true.
Proof.
  intros. apply H. apply H0.
Qed.

Theorem silly3_firsttry : forall (n : nat),
    (true = (n =? 5)) ->
    (S (S n)) =? 7 = true.
Proof.
  intros n H. simpl. symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
  intros l l' H. rewrite -> H.
  symmetry. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m).
  apply eq2. apply eq1.
Qed.

Theorem S_injective : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
  intros n m H.
  inversion H as [Hnm].
  reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    j = z :: l ->
    x = y.
Proof.
  intros X x y z l j eq1 eq2. injection eq1 as H1 H2.
  rewrite -> H1. rewrite <- H2 in eq2. injection eq2 as H3.
  symmetry. apply H3.
Qed.

Theorem eqb_0_l : forall n,
    0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl.
    intros H. discriminate H.
Qed.


Theorem discriminate_ex1 : forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j contra. discriminate contra. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
    (S n) =? (S m) = b ->
    n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
    (n =? 5 = true -> (S (S n)) =? 7 = true) ->
    true = (n =? 5) ->
    true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem double_injective_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.

Theorem double_injective : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + apply f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal.
Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros m. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate.
  - simpl. intros m. destruct m as [| m'] eqn:E.
    + discriminate.
    + intros H. apply f_equal. apply IHn' in H. apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros m. destruct m.
    + simpl. reflexivity.
    + discriminate.
  - simpl. intros m. destruct m.
    + simpl. discriminate.
    + intros H. apply f_equal.
      apply IHn'. simpl in H. inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1. reflexivity.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h l' IHl'].
  - simpl. intros n H. destruct n.
    + reflexivity.
    + reflexivity.
  - intros n H. simpl. destruct n as [| n'] eqn:E.
    + discriminate.
    + apply IHl'.
      simpl in H. inversion H.
      reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
       else false.
Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - (* n =? 3 = true *) reflexivity.
  - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
    + (* n =? 5 = true *) reflexivity.
    + (* n =? 5 = false *) reflexivity. Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| h l' IHl'].
  - intros l1 l2 H.
    simpl in H. inversion H.
    simpl. reflexivity.
  - intros l1 l2 H.
    destruct h as [f s]. simpl in H.
    destruct (split l') as [f' s']. inversion H.
    simpl. apply f_equal. apply IHl'. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
       else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
  - (* e3 = true *) apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
    (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allowing us to finish the
        proof. *)
    destruct (n =? 5) eqn:Heqe5.
    + (* e5 = true *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + (* e5 = false *) discriminate eq. Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct (f b) eqn:E.
  - destruct b.
    + rewrite -> E. apply E.
    + destruct (f true) eqn:E_f_true.
      * apply E_f_true.
      * apply E.
  - destruct b.
    + destruct (f false) eqn:E_f_false.
      * apply E.
      * apply E_f_false.
    + rewrite -> E. apply E.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros. generalize dependent n.
  induction m as [| m' IHm'].
  - intros n. destruct n.
    + reflexivity.
    + simpl. reflexivity.
  - intros n. induction n as [| n' IHn'].
    + simpl. reflexivity.
    + simpl. apply IHm'.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros. apply eqb_true in H. apply eqb_true in H0.
  rewrite -> H0 in H. rewrite -> H.
  rewrite <- eqb_refl. reflexivity.
Qed.

Definition split_combine_statement : Prop :=
  forall X Y (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l1. induction l1 as [| h1 l1' IHl1'].
  - intros. simpl. destruct l2.
    + reflexivity.
    + discriminate.
  - intros. inversion H. destruct l2 as [| h2 l2'].
    + simpl. discriminate.
    + inversion H1. apply IHl1' in H2.
      simpl. rewrite H2. reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l. induction l as [| h l' IHl'].
  - simpl. discriminate.
  - intros. destruct (test h) eqn:Hh.
    + simpl in H. rewrite -> Hh in H.
      inversion H. rewrite -> H1 in Hh. apply Hh.
    + simpl in H. rewrite -> Hh in H.
      apply IHl' in H. apply H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => andb (test h) (forallb test t)
  end.

Example test_forallb1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity.  Qed.
Example test_forallb2 : forallb negb [false;false] = true.
Proof. reflexivity.  Qed.
Example test_forallb3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity.  Qed.
Example test_forallb4 : forallb (eqb 5) [] = true.
Proof. reflexivity.  Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => orb (test h) (existsb test t)
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros. induction l as [| h l' IHl'].
  - unfold existsb'. simpl. reflexivity.
  - simpl. rewrite -> IHl'.
    unfold existsb'. unfold forallb.
    destruct (test h) eqn:Eq.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
