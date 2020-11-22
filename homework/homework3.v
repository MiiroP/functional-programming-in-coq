From LF Require Export Lists.

Import NatList.

Fixpoint remove_one (n:nat) (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match (eqb h n) with
              | true => t
              | false => h :: (remove_one n t)
              end
  end.

Example test_remove : remove_one 1 [2;1;3;1;4;1] = [2;3;1;4;1].
Proof. reflexivity. Qed.

Fixpoint replace_one (n m:nat)(l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match (eqb h n) with
              | true => m :: t
              | false => h :: (replace_one n m t)
              end
  end.

Example test_replace : replace_one 1 5 [2;1;3;1;4;1] = [2;5;3;1;4;1].
Proof.  reflexivity. Qed.

Fixpoint insert (n:nat)(l:natlist) : natlist :=
  match l with
  | nil => n :: nil
  | h :: t => match (leb h n) with
              | true => h :: (insert n t)
              | false => n :: h :: t
              end
  end.

Example test_insert : insert 5 [1;3;4;6;6] = [1; 3; 4; 5; 6; 6].
Proof.  reflexivity. Qed.

Fixpoint insertion_sort (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Example test_insertion_sort : insertion_sort [2;4;1;6;9;6;4;1;3;5;10] = [1;1; 2; 3; 4; 4; 5; 6; 6; 9; 10].
Proof. reflexivity. Qed.

Fixpoint total (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => (plus h (total t))
  end.

Example test_total : total [1; 2; 3; 4; 5; 6; 7] = 28.
Proof. reflexivity. Qed.

Compute total [1; 2; 3; 4; 5; 6; 7].
