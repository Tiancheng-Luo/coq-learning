Module Playground1.

Inductive bool : Type :=
| true : bool
| false : bool.

Check true.
Check bool.

Check True.
Check (forall x : bool, x=x).

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

(* comment *)

(* Haskell: data Nat = O | S Nat *)

Check (S (S (S O))).


End Playground1.

Print Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S O))).
Eval simpl in (minustwo 4).

Check minustwo.
Check S.
Check pred.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Print evenb.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1 : oddb (S O) = true.
Proof. unfold oddb. (* unfold evenb. *) simpl. reflexivity. Qed.

Example test_oddb2 : oddb 4 = false.
Proof. reflexivity. Qed.


Module Playground2.

Definition admit {T: Type} : T.  Admitted.

(* Haskell: undefined *)

Fixpoint plus (n : nat) (m : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(* Comment about struct *)

Theorem three_plus_two : plus 3 2 = 5.
Proof. reflexivity. Qed.

Fixpoint mult (n m : nat) : nat :=
  match n with 
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O   , _    => O
    | _   , O    => n          (* make this non-overlapping *)
    | S n', S m' => minus n' m'
  end.

Print minus.

End Playground2.

Print minus.

Example test_mult1 : (mult 3 4) <> 9.
Proof. simpl. discriminate. Qed.

Notation "x + y" := (plus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y)  
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y)  
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(* Explain the difference: *)
Eval simpl in (forall n:nat, 0 + n = n).

Eval simpl in (forall n:nat, n + 0 = n).

(* End of first seminar. *)
