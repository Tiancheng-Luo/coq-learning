Require Import Arith.

Theorem nat_ind_le : forall P : nat -> Prop,
    P 0 -> (forall n, (forall m, m <= n -> P m) -> P (S n))
    -> forall n, P n.
Proof.
  intros P HP0 HPi.
  set (Q n := forall m, m <= n -> P m).
  assert (forall n : nat, Q n).
    intros.
    induction n.
      unfold Q.
      intros.
      inversion H. exact HP0.

      unfold Q.
      intros.
      apply le_lt_eq_dec in H.
      destruct H as [Hl | Heq].
        unfold lt in Hl. apply le_S_n in Hl.
        apply IHn. exact Hl.

        rewrite Heq.
        apply HPi.
        exact IHn.

  intro.
  apply (H n).
  apply le_n.
Qed.

Ltac induction_le_nat n := let IHn := fresh "IH" n in 
  try intros until n; pattern n; apply nat_ind_le; clear n; [ | intros n IHn ].


Theorem nat_ind_lt : forall P : nat -> Prop,
    (forall n, (forall m, m < n -> P m) -> P n)
    -> forall n, P n.
Proof.
  intros P HPi.
  set (Q n := forall m, m <= n -> P m).
  assert (forall n : nat, Q n).
    intros.
    induction n.
      unfold Q.
      intros.
      inversion H.
      apply HPi.
      intros.
      contradict H1.
      apply lt_n_0.

      unfold Q.
      intros.
      apply le_lt_eq_dec in H.
      destruct H as [Hl | Heq].
        unfold lt in Hl. apply le_S_n in Hl.
        apply IHn. exact Hl.

        rewrite Heq.
        apply HPi.
        intros.
        apply le_S_n in H.
        apply IHn. exact H.

  intro.
  apply (H n).
  apply le_n.
Qed.

Ltac induction_lt_nat n := let IHn := fresh "IH" n in 
  try intros until n; pattern n; apply nat_ind_lt; clear n; intros n IHn.



Theorem nat_pred_interval_dec : forall P : nat -> Prop, (forall n, {P n} + {~ P n})
    -> forall n m, {exists k, n <= k < m /\ P k} + {forall k, n <= k < m -> ~ P k}.
Proof.
  intros.
  induction m.
    right.
    intros.
    destruct H0.
    inversion H1.

    destruct (le_lt_dec n m) as [Hnm | Hmn].
    (* Case where n <= m *)
    destruct IHm as [Heg | Hnall].
      left.
      destruct Heg as [k [Hnkm HPk]].
      exists k.
      split. destruct Hnkm as [Hnk Hkm]. split. assumption.
      apply le_S. apply Hkm. assumption.

      destruct (H m) as [HPm | HnPm].
      left. exists m.
      split. split. assumption. apply le_n. assumption.

      right.
      intros.
      destruct H0 as [Hnk Hkm].
      apply le_lt_eq_dec in Hkm.
      destruct Hkm as [Hkm | Hkm].
        apply Hnall. split. assumption.
        apply lt_S_n; assumption.

        inversion Hkm. assumption.


    (* Case where m < n *)
    right. clear H. clear IHm.
    intros. exfalso.
    assert (n <= m). destruct H as [Hnk Hkm].
    apply le_S_n in Hkm.
    apply le_trans with (m := k); assumption.
    (* SearchAbout (_<=_ -> ~_<_). *)
    revert Hmn. apply le_not_lt. assumption.
Qed.

Theorem exists__not_forall_not : forall (S : Set) (P Q : S -> Prop),
    (exists x : S, Q x /\ P x) -> ~ forall x : S, Q x -> ~ P x.
Proof.
  intros.
  intro.
  destruct H as [x [Qx Px]].
  unfold not in H0. apply H0 with (x := x) ; assumption.
Qed.
