
Require Import Com.

Definition update (s : state) x v y := if String.string_dec x y then v else s y.

Inductive big_step : com * state -> state -> Prop :=
| SkipSem : forall s, big_step (Skip, s) s
| AssignSem : forall s x a, big_step (Assign x a, s) (update s x (aval s a))
| SeqSem : forall c1 c2 s1 s2 s3, big_step (c1, s1) s2 -> big_step (c2, s2) s3 ->
                                  big_step (Seq c1 c2, s1) s3
| IfTrue : forall b c1 c2 s s', bval s b = true -> big_step (c1, s) s' ->
                                big_step (If b c1 c2, s) s'
| IfFalse : forall b c1 c2 s s', bval s b = false -> big_step (c2, s) s' ->
                                 big_step (If b c1 c2, s) s'
| WhileFalse : forall b c s, bval s b = false ->
                             big_step (While b c, s) s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b = true -> big_step (c, s1) s2 -> big_step (While b c, s2) s3 ->
    big_step (While b c, s1) s3.

Notation "A ==> B" := (big_step A B) (at level 80, no associativity).

Lemma lem_test_if : forall b s s', (If b Skip Skip, s) ==> s' -> s = s'.
Proof.
  scrush.
Qed.

Lemma lem_assign_simp :
  forall a x s s', (Assign x a, s) ==> s' <-> s' = update s x (aval s a).
Proof.
  sauto.
Qed.

Lemma lem_seq_assoc : forall c1 c2 c3 s s', (Seq c1 (Seq c2 c3), s) ==> s' <->
                                            (Seq (Seq c1 c2) c3, s) ==> s'.
Proof.
  pose SeqSem; sauto; eauto.
Qed.

Definition equiv_com (c1 c2 : com) := forall s s', (c1, s) ==> s' <-> (c2, s) ==> s'.

Notation "A ~~ B" := (equiv_com A B) (at level 70, no associativity).

Lemma lem_while_unfold : forall b c, While b c ~~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equiv_com.
  intros; split.
  - intro H; inversion H; pose SkipSem; pose SeqSem; pose IfFalse; pose IfTrue; eauto.
  - intro H; inversion H; pose WhileTrue; pose WhileFalse; sauto; eauto.
Qed.

Lemma lem_triv_if : forall b c, If b c c ~~ c.
Proof.
  unfold equiv_com; sauto.
  - scrush.
  - destruct (bval s b) eqn:?.
    + eauto using IfTrue.
    + eauto using IfFalse.
Qed.


Lemma lem_commute_if :
  forall b1 b2 c11 c12 c2,
    If b1 (If b2 c11 c12) c2 ~~ If b2 (If b1 c11 c2) (If b1 c12 c2).
Proof.
  unfold equiv_com; split; intro H.
  - inversion H; subst.
    + pose IfFalse; pose IfTrue; scrush.
    + destruct (bval s b2) eqn:?; eauto using IfFalse, IfTrue.
  - inversion H; pose IfFalse; pose IfTrue; scrush.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', (While b c, s) ==> s' -> c ~~ c' ->
                                               (While b c', s) ==> s'.
Proof.
  assert (forall p s', p ==> s' -> forall b c c' s,
              p = (While b c, s) -> c ~~ c' -> (While b c', s) ==> s'); [idtac | scrush].
  intros p s' H.
  induction H; sauto.
  - Reconstr.hobvious Reconstr.AllHyps
		      (@WhileFalse)
		      Reconstr.Empty.
<<<<<<< HEAD
  - Reconstr.hsimple (@IHbig_step2, @H0, @H3, @H)
		(@WhileTrue)
		(@equiv_com).
=======
  - Reconstr.hsimple Reconstr.AllHyps
		     (@WhileTrue)
		     (@equiv_com).
>>>>>>> 5d208fb92cc65c2d08cbeb8f1959db0c15030ac3
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b c ~~ While b c'.
Proof.
  Reconstr.hobvious Reconstr.Empty
		    (@lem_while_cong_aux)
		    (@equiv_com).
Qed.

Lemma lem_sim_refl : forall c, c ~~ c.
Proof.
  scrush.
Qed.

Lemma lem_sim_sym : forall c c', c ~~ c' -> c' ~~ c.
Proof.
  scrush.
Qed.

Lemma lem_sim_trans : forall c1 c2 c3, c1 ~~ c2 -> c2 ~~ c3 -> c1 ~~ c3.
Proof.
  unfold equiv_com; scrush.
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1 s2, (c, s) ==> s1 -> (c, s) ==> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 1.
  - scrush.
  - intros s0 H2; inversion H2; scrush.
Qed.
