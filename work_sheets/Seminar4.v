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

Definition admit {T: Type} : T.  Admitted.
(* Haskell: undefined *)

Module Playground2.

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

(* Require Import Arith. *)
Search nat.
SearchAbout nat.
(* SearchPattern (_ -> nat).    (* Doesn't work in older coq versions *) *)
SearchRewrite (0 + _).


(* More tactics. *)

Theorem plus_id_example : forall n m,
                            n = m -> n + n = m + m.
Proof.
  intros k l.
  intros H.
  rewrite <- H.                    (* show directions *)
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
  intros.
  (* destruct n; reflexivity. *)
  destruct n.
    reflexivity.

    reflexivity.
Qed.

Axiom convenient : forall n, n+1 = S n.

Theorem plus_1_neq_0 : forall n : nat, n + 1 <> 0.
Proof.
  intros.
  (* rewrite convenient. *)
  (* discriminate. *)
  destruct n.
    discriminate.

    simpl.
    discriminate.
Qed.

Theorem eq_beq_nat : forall n m : nat,
    n = m <-> beq_nat n m = true.
Proof.
  intros.
  split.
    intro.
    rewrite H.
(* Finish from here. Hard. Good HW! :) *)
Admitted.


Theorem plus_0_r : forall n, n + 0 = n.
Proof.
  intros.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem minus_diag : forall n : nat, n - n = 0.
Proof.
  intros.
  induction n.
    reflexivity.

    simpl.
    assumption.
Qed.

Theorem plus_comm : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
    simpl.
    rewrite plus_0_r.
    reflexivity.

    simpl.
    rewrite IHn.
    assert (forall k l, k + S l = S (k + l)).
      clear IHn n m.
      intros.
      induction k.
        reflexivity.

        simpl.
        rewrite IHk.
        reflexivity.

    rewrite H.
    reflexivity.
Qed.
(* HW: do without assert, but with induction within induction. *)

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
  intros n.
  induction n.
    intros.
    simpl in H.
    destruct m.
      reflexivity.

      simpl in H.
      discriminate H.

   (* induction side *)
   intros.
   destruct m.
     discriminate H.

     (* apply a hypothesis to the goal *)
     f_equal.                   (* remove the same constructor *)
     apply IHn.
     simpl in H.
     (* TODO(klao): look up how to introduce S-es to the goal. *)
     (* union of 'discriminate' and 'f_equal in hypothesis' *)
     inversion H.
     reflexivity.
Qed.
(* TODO(klao): look into: printing readable proofs. *)

(* End of Seminar 2. *)

(* ********************************************************************** *)
(* Seminar 3 starts here. *)

(* revert, generalize dependent, and induction in |- *)



Theorem plus_rearrange : forall n m p q,
    (n + m) + (p + q) = (m + n) + (q + p).
Proof.
  intros.
  rewrite plus_comm.
  rewrite plus_comm.
  Check plus_comm.

  rewrite (plus_comm n m).
  (* rewrite (plus_comm p q). *)
  (* reflexivity. *)
  replace (p + q) with (q + p).
  reflexivity.
  apply plus_comm.
Qed.

(* ************* *)
(* 'Apply' and other tactic examples *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* intros. *)
  (* apply H. *)
  (* exact H0. *)

  intro H.
  (* apply H. *)
  exact (H 3).
Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.

  symmetry.
  (* simpl. *) (* Actually, this [simpl] is unnecessary, since 
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
  remember H as H1.
  clear HeqH1.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    intros. destruct m as [| m']. reflexivity.
    simpl in H. discriminate H.

    intros. destruct m as [| m']. discriminate H.
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

(* HW *)
Theorem bool_funcs : forall (f : bool -> bool),
  (forall b, f (f b) = f b) \/ (forall b, f b = negb b).
Admitted.

Theorem bool_fn_applied_thrice' : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intro f.
  destruct (bool_funcs f).
    intro.
    rewrite H.
    rewrite H.
    reflexivity.

    intro.
    rewrite !H.
    (* SearchAbout negb. *)
    rewrite Bool.negb_involutive.
    reflexivity.
Qed.

(* Seminar 3 ended here. *)
(* ********************************************************** *)
(* Seminar 4 starts here. *)


Module ExampleList1.

Inductive list (T : Type) : Type :=
  | nil
  | cons : T -> list T -> list T.

Check (cons nat 2 (cons nat 1 (nil nat))).

Check (cons _ 2 (cons _ 1 (nil _))).

Check cons.
Check nil.

End ExampleList1.

Module ExampleList2.

Set Implicit Arguments.

Inductive list (T : Type) : Type :=
  | nil
  | cons : T -> list T -> list T.

Check (cons 2 (cons 1 (nil _))).

Implicit Arguments nil [[T]].
(* Deprecated, use: Arguments nil [T]. *)

Check (cons 2 (cons 1 nil)).

Unset Implicit Arguments.

Fixpoint length {X:Type} (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length t)
  end.

Eval compute in length (cons 2 (cons 1 nil)).

Check @length.

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

(* Define app! *)
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
    | [] => l2
    | h :: t => h :: app t l2
  end.

Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).


Eval compute in [1,2,3] ++ 4::5::[].

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X := 
  match count with
    | O => nil
    | S c' => x :: repeat x c'
  end.

Eval compute in repeat true 3.

Theorem repeat_length : forall n X (x : X), length (repeat x n) = n.
Admitted.

(* Induction priciple for induction definition. *)

Check nat_ind.
Check list_ind.

Theorem app_assoc : forall X (l1 l2 l3 : list X), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
Admitted.

(* HW: trivial *)
Theorem app_length : forall X (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Admitted.

(* HW: involved. What should the induction go on? *)
Theorem app_length2 : forall X (l1 l2 : list X) n1 n2,
     length l1 = n1 -> length l2 = n2 -> length (l1 ++ l2) = n1 + n2.
Admitted.


Inductive vector (T : Type) : nat -> Type :=
  | nilv : vector T 0
  | consv n : T -> vector T n -> vector T (S n).

Implicit Arguments nilv [[T]].
Implicit Arguments consv [[T] [n]].

Check consv 1 (consv 2 nilv).

Fixpoint lengthv {T : Type} {n : nat} (v : vector T n) : nat := admit.

Fixpoint repeatv {X : Type} (x : X) (n : nat) : vector X n := admit.

Theorem lengthv_repeatv : forall n X (x : X), lengthv (repeatv x n) = n.
Proof.
Admitted.
(* Show that simpl is not enough here, but compute is, or unfold. *)

Check @repeat.
Check @repeatv.

(* Relation of 'forall' and '->' *)

Parameter p q : Prop.

Print p.

Definition p_to_q := forall h : p, q.

Print p_to_q.

Check forall n : nat, bool.

Check forall n : nat, p.


End ExampleList2.
