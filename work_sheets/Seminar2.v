Module Playground1.

Inductive bool : Type :=
| true : bool
| false : bool.


Inductive nat : Type :=
| O : nat
| S : nat -> nat.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).


Module Playground2.

Definition admit {T: Type} : T.  Admitted.

(* Haskell: undefined *)

Fixpoint plus (n : nat) (m : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

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

End Playground2.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(* End of seminar 1. *)

(* ************************************************************ *)

(* Looking up info *)

Search nat.
SearchAbout nat.
(* SearchPattern (nat -> bool).    (* Doesn't work in older coq versions *) *)
SearchRewrite (0 + _).
(* Require Import Arith. *)


(* More tactics. *)

Theorem plus_id_example : forall n m : nat,
                            n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite H.                    (* show directions *)
  reflexivity.
Qed.

Theorem mult_O_plus : forall n m : nat,
                        (0 + n) * m = n * m.
Proof.
  intros.
  rewrite -> plus_O_n.
  reflexivity.
Qed.


Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | S n', S m' => beq_nat n' m'
    | _, _ => false
  end.

Print beq_nat.

Theorem plus_1_neq_0_b : forall n : nat,
                           beq_nat (n+1) 0 = false.
Proof.
Admitted.

Theorem plus_1_neq_0 : forall n : nat, n + 1 <> 0.
Proof.
Admitted.

Theorem eq_beq_nat : forall n m : nat,
    n = m <-> beq_nat n m = true.
Admitted.



Theorem plus_0_r : forall n, n + 0 = n.
Proof.
Admitted.

Theorem minus_diag : forall n : nat, n - n = 0.
Proof.
Admitted.


Theorem plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m.
  revert m.
Admitted.    

(* Induction more closely *)

Fixpoint double n : nat :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
Admitted.
(* revert, generalize dependent, and induction in |- *)

Theorem plus_rearrange : forall n m p q,
    (n + m) + (p + q) = (m + n) + (q + p).
Proof.
  intros.
  rewrite plus_comm.
  rewrite plus_comm.
  rewrite (plus_comm n m).
  replace (p + q) with (q + p).
  reflexivity.
  apply plus_comm.
Qed.

(* ************* *)
(* 'Apply' and other tactic examples *)
(* TODO: where to put this? *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
Admitted.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  apply H.
Qed.

(* Reasoning in assumptions, aka forward reasoning. *)
Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    intros. destruct m. reflexivity. simpl in H. discriminate H.

    intros. destruct m. simpl in H. discriminate H.
    simpl in H. rewrite <- !plus_n_Sm in H.  (* rewrite modifiers *)
    inversion H. apply IHn' in H1. rewrite H1. reflexivity.
Qed.


(* Remember and destruct expression. *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  Case "b = true".
  remember (f true) as ftrue.
    destruct ftrue.
    SCase "f true = true".
      rewrite <- Heqftrue.
      symmetry.
      apply Heqftrue.
    SCase "f true = false".
      remember (f false) as ffalse.
      destruct ffalse.
      SSCase "f false = true".
        symmetry.
        apply Heqftrue.
      SSCase "f false = false".
        symmetry.
        apply Heqffalse.
  remember (f false) as ffalse.
    destruct ffalse.
    SCase "f false = true".
      remember (f true) as ftrue.
      destruct ftrue.
      SSCase "f true = true".
        symmetry.
        apply Heqftrue.
      SSCase "f true = false".
        symmetry.
        apply Heqffalse.
    SCase "f false = false".
      rewrite <- Heqffalse.
      symmetry.
      apply Heqffalse.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.
Qed.


(* ******************** *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst p :=
  match p with
    | pair x y => x
  end.

Check fst.

Definition snd p :=
  match p with
    | pair x y => y
  end.

Notation "( x , y )" := (pair x y). (* Spaces are important! *)

Eval simpl in (fst (3,4)).

Definition swap_pair p :=
  match p with
    | (x, y) => (y, x)
  end.

Theorem surjective_pairing : forall p : natprod,
    p = (fst p, snd p).
Proof.
Admitted.

(* ******************** *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).
Print l_123.

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Print l_123.

Example list_notation : l_123 = 1 :: 2 :: 3 :: [].
Proof. reflexivity. Qed.

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S c' => cons n (repeat n c')
  end.

Fixpoint length l :=
  match l with
    | nil => 0
    | x :: xs => S (length xs)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: app t l2
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Example test_app : [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.

Definition hd l :=
  match l with
    | nil => 0
    | h :: t => h
  end.

Definition tl l :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
Proof.
  intro.
  destruct l as [| l'].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

(* Induction priciple for induction definition. *)

Check nat_ind.
Check natlist_ind.

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1.
    simpl. reflexivity.
    simpl. f_equal. apply IHl1.
Qed.


Module GenericList.

Set Implicit Arguments.

Inductive list (T : Type) : Type :=
  | nil
  | cons : T -> list T -> list T.

Check (cons 2 (cons 1 (nil _))).

Implicit Arguments nil [[T]].
(* Deprecated, use: Arguments nil [T]. *)

Check (cons 2 (cons 1 nil)).


End GenericList.
