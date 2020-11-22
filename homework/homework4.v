From LF Require Export Lists.

Import NatList.
Import PartialMap.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| n1 l1' IHl1'].
  - simpl. rewrite -> app_assoc. reflexivity.
  - simpl. rewrite <- IHl1'. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n1 l1' IHl1'].
  - simpl. reflexivity.
  - simpl.
    destruct n1 as [| n1'].
    + rewrite -> IHl1'. reflexivity.
    + rewrite -> IHl1'. simpl. reflexivity.
Qed.

Lemma n_leq_Sn : forall n : nat,
    n <=? S n = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count : forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' IHs'].
  - simpl. reflexivity.
  - simpl.
    destruct n as [| n'].
    + simpl. rewrite -> n_leq_Sn. reflexivity.
    + simpl. rewrite -> IHs'. reflexivity.
Qed.

Search rev.

Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem update_eq : forall (d : partial_map) (x : id) (v : nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. destruct d as [| x' v' d'].
  - destruct x. simpl.
    rewrite <- eqb_refl. reflexivity.
  - destruct x. simpl.
    rewrite <- eqb_refl. reflexivity.
Qed.
