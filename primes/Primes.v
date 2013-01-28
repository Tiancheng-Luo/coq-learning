Require Import Arith.
Require Omega.

(* TODO(klao): remove this module after explaining the differences
with the 'Inductive' approach. *)
Module Primes0.

(* 'divides' predicate. *)
(* TODO(klao): replace with an inductive one! *)

Definition divides (a c : nat) : Prop :=
  exists b, a*b = c.

Notation "( a | c )" := (divides a c) (at level 0) : nat_scope.


(* 'prime' predicate. *)
(* TODO(klao): replace with an inductive one. *)

Definition prime (n : nat) : Prop :=
  n > 1 /\ forall d, (d | n) -> d = 1 \/ d = n.

Definition composite (n : nat) : Prop :=
  exists k, exists l, k > 1 /\ l > 1 /\ n = k*l.

Theorem modus_tollens : forall a b : Prop, (a -> b) -> (~b -> ~a).
Proof.
  unfold not.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.



Theorem composite_not_prime : forall n : nat,
  composite n -> ~ prime n.                                
Proof.
  unfold composite, prime, not.
  intros.
  destruct H as [k [l [Hk [Hl Hkl]]]].
  assert (k | n) as Hkdivn.
    exists l. auto.

  destruct H0 as [Hn Hpr].
  apply Hpr in Hkdivn.
  destruct Hkdivn as [Hk1 | Hkn].
  omega.
  assert (k < n).
    rewrite mult_comm in Hkl.
    inversion Hl as [H | m H0 H]; rewrite <- H in Hkl. omega.
    simpl in Hkl.
    assert (0 < m*k).
    SearchAbout (0 < _ * _).
    apply NPeano.Nat.mul_pos_pos; omega.
    omega.

  omega.
Qed.

End Primes0.


Module Primes.

(* 'divides' predicate. *)
Inductive divides (a : nat) : nat -> Prop :=
  divs b : divides a (a*b).

Notation "( a | c )" := (divides a c) (at level 0) : nat_scope.


(* 'prime' predicate. *)
Inductive prime (n : nat) : Prop :=
  prim : n > 1 -> (forall d, 1 < d < n -> ~ (d | n)) -> prime n.


Inductive composite : nat -> Prop :=
  comps k l : k > 1 -> l > 1 -> composite (k*l).


(* TODO: find a simple proof for stuff like this! Or some existing tools. *)
Theorem mult_gt_parts : forall k l, k > 1 -> l > 1 -> k*l > k.
Proof.
  intros.
  rewrite mult_comm.
  destruct l. omega.
  simpl.
  remember (l * k) as lk.
  assert (1 < lk).
    rewrite Heqlk.
    rewrite mult_comm.
    apply NPeano.Nat.lt_1_mul_pos; omega.
  clear Heqlk.
  omega.
Qed.

Theorem composite_not_prime : forall n : nat,
  composite n -> ~ prime n.                                
Proof.
  unfold not.
  intros n Hc Hp.
  destruct Hc as [k l Hk Hl].
  destruct Hp as [_ Hp].
  assert (k < k * l) as Hkl1.
    apply mult_gt_parts; assumption.

  assert (k = k * l) as Hkl2.
    contradiction Hp with (d := k).
    split. assumption. exact Hkl1.
    apply divs.

  omega.
Qed.

Theorem prime_not_composite : forall n : nat,
  prime n -> ~ composite n.
Proof.
  unfold not.
  intros. revert H.
  apply composite_not_prime.
  assumption.
Qed.

Theorem not_prime_composite : forall n : nat, n > 1 -> ~ prime n -> composite n.
Proof.
  unfold not.
  intros.
Admitted.


(* Not a good idea: separate into prime decidability and ~ prime -> composite. Or is it? *)
Theorem prime_or_composite : forall n : nat, n > 1 -> {prime n} + {composite n}.
Proof.
  intros.
  assert (forall d, {(d | n)} + {~(d | n)}).
    intros.
    SearchAbout NPeano.div.
Admitted.

End Primes.
