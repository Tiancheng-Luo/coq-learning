Require Import Arith.

Check nat_ind.

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
