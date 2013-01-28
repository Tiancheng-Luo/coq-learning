Require Import Arith.
Require Omega.
Require Import Induction.

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


(* TODO(klao): prove directly without div? *)
Theorem divisible_dec : forall d n : nat, {(d | n)} + {~(d | n)}.
Proof.
  intros.
  destruct (eq_nat_dec d 0) as [Hd0 | Hdn0].
    destruct n. left. rewrite Hd0. apply (divs 0 0).
      right. intro. inversion H. rewrite Hd0 in H1. discriminate H1.

    (* d <> 0 *)
    pose (NPeano.div_mod n d Hdn0) as Hnd. clearbody Hnd.
    remember (NPeano.modulo n d) as n_mod_d.
    destruct n_mod_d.
      rewrite plus_0_r in Hnd.
      left. rewrite Hnd. apply divs.

      right. intro. inversion H. clear H.
      symmetry in H0. pose H0 as H1.
      apply (NPeano.Nat.div_unique_exact n d b Hdn0) in H1.
      rewrite H1 in H0.
      rewrite Hnd in H0 at 1.
      rewrite <- plus_0_r in H0.
      apply NPeano.Nat.add_cancel_l in H0.
      discriminate H0.
Qed.

Theorem prime_or_composite : forall n : nat, n > 1 -> {prime n} + {composite n}.
Proof.
  intros.
  assert ({exists d, 1 < d < n /\ (d | n)} + {forall d, 1 < d < n -> ~(d | n)}).
    apply nat_pred_interval_dec. intro. apply divisible_dec.
  destruct H0 as [ Hc | Hp ].
    right.
    destruct Hc as [d [[H1d Hdn] Hddivn]].
    inversion Hddivn. clear Hddivn.
    apply comps. assumption.
      destruct (le_gt_dec b 1) as [Hb1 | Hb1].
        assert (d * b <= d).
          rewrite <- mult_1_r.
          apply mult_le_compat_l. assumption.
        rewrite H0 in H1.
        omega. (* Hdn -><- H1 *)

        assumption.

    left.
    apply prim; assumption.
Qed.

Theorem divides_trans : forall a b c, (a | b) -> (b | c) -> (a | c).
Proof.
  intros.
  inversion H0.
  inversion H.
  rewrite <- mult_assoc.
  apply divs.
Qed.

Theorem prime_divisor : forall n : nat, n > 1 -> exists p, prime p /\ (p | n).
Proof.
  (* TODO(klao): fix induction_lt_nat tactic, so it works after intros here. *)
  induction_lt_nat n.
  intro Hn1.
  destruct (prime_or_composite n Hn1) as [Hp | Hc].
    exists n.
    split. exact Hp.
    rewrite <- mult_1_r.
    apply divs.

    destruct Hc.
    assert (k < k * l). apply mult_gt_parts; assumption.
    pose (IHn k H1 H) as Hpk.
    destruct Hpk as [p [Hp Hpdivk]].

    exists p.
    split. assumption.
    apply divides_trans with (b := k).
    assumption.
    apply divs.
Qed.


End Primes.
