From LF Require Export Poly.

Theorem rev_app_distr : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n1 l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
      rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.
Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l,
   filter (fun x => (negb (test x))) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

