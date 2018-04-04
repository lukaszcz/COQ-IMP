
Require Import Com.
Require Import Big_Step.
Require Import Star.

Inductive small_step : com * state -> com * state -> Prop :=
| AssignSemS : forall x a s, small_step (Assign x a, s) (Skip, update s x (aval s a))
| SeqSemS1 : forall c s, small_step (Seq Skip c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', small_step (c1, s) (c1', s') ->
                                    small_step (Seq c1 c2, s) (Seq c1' c2, s')
| IfTrueS : forall b c1 c2 s, bval s b = true ->
                              small_step (If b c1 c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, bval s b = false ->
                               small_step (If b c1 c2, s) (c2, s)
| WhileS : forall b c s, small_step (While b c, s) (If b (Seq c (While b c)) Skip, s).

Notation "A --> B" := (small_step A B) (at level 80, no associativity).

Notation "A -->* B" := (star small_step A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall c s s1 s2, (c, s) --> s1 -> (c, s) --> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H.
  revert s2.
  induction H; try yelles 2.
  intros s2 H2; inversion H2; scrush.
Qed.

(* Equivalence with big-step semantics *)

Lemma lem_star_seq2 : forall c1 c2 s c1' s', (c1, s) -->* (c1', s') ->
                                             (Seq c1 c2, s) -->* (Seq c1' c2, s').
Proof.
  assert (forall p1 p2, p1 -->* p2 ->
                        forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                               (Seq c1 c2, s) -->* (Seq c1' c2, s')); [idtac|scrush].
  intros p1 p2 H.
  induction H; sauto.
  destruct y; sauto.
  pose @star_step; pose SeqSemS2; scrush.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3, (c1, s1) -->* (Skip, s2) -> (c2, s2) -->* (Skip, s3) ->
                                            (Seq c1 c2, s1) -->* (Skip, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((Seq c1 c2, s1) -->* (Seq Skip c2, s2)).
  pose lem_star_seq2; scrush.
  assert ((Seq Skip c2, s2) -->* (c2, s2)).
  pose @star_step; scrush.
  pose @lem_star_trans; scrush.
Qed.

Lemma lem_big_to_small : forall p s', p => s' -> p -->* (Skip, s').
Proof.
  intros p s' H.
  induction H as [ | | | | | | b c s1 s2 ]; try yelles 1.
  - pose @star_step; scrush.
  - Reconstr.hobvious Reconstr.AllHyps
		      (@lem_seq_comp)
		      Reconstr.Empty.
  - pose @star_step; pose IfTrueS; scrush.
  - pose @star_step; pose IfFalseS; scrush.
  - pose @star_step; pose WhileS; pose IfFalseS; scrush.
  - assert ((While b c, s1) -->* (Seq c (While b c), s1)).
    pose @star_step; pose WhileS; pose IfTrueS; scrush.
    assert ((Seq c (While b c), s1) -->* (Seq Skip (While b c), s2)).
    Reconstr.hobvious Reconstr.AllHyps
		      (@lem_star_seq2)
		      Reconstr.Empty.
    pose @lem_star_trans; pose @star_step; pose SeqSemS1; scrush.
Qed.

Lemma lem_small1_big_continue : forall p p', p --> p' -> forall s, p' => s -> p => s.
Proof.
  intros p p' H.
  induction H; try yelles 1.
  - Reconstr.hobvious Reconstr.Empty
		      (@Big_Step.SeqSem, @Big_Step.SkipSem, @lem_big_to_small)
		      Reconstr.Empty.
  - sauto; Reconstr.hobvious Reconstr.AllHyps
		             (@Big_Step.SeqSem)
		             Reconstr.Empty.
  - Reconstr.htrivial Reconstr.AllHyps
		      (@Big_Step.IfTrue)
		      Reconstr.Empty.
  - Reconstr.htrivial Reconstr.AllHyps
		      (@Big_Step.IfFalse)
		      Reconstr.Empty.
  - Reconstr.htrivial Reconstr.Empty
		      (@Big_Step.lem_while_unfold, @Big_Step.SkipSem)
		      (@Big_Step.equiv_com).
Qed.

Lemma lem_small_to_big : forall p s, p -->* (Skip, s) -> p => s.
Proof.
  assert (forall p p', p -->* p' -> forall s, p' = (Skip, s) -> p => s); [idtac|scrush].
  intros p p' H.
  induction H; sauto.
  Reconstr.hsimple Reconstr.AllHyps
		   (@lem_small1_big_continue)
		   Reconstr.Empty.
Qed.

Corollary cor_big_iff_small : forall p s, p => s <-> p -->* (Skip, s).
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@lem_small_to_big, @lem_big_to_small)
		    Reconstr.Empty.
Qed.

(* Final configurations and infinite reductions *)

Definition final (cs : com * state) := ~(exists cs', cs --> cs').

Lemma lem_nonfinal_dec_0 :
  forall c s, (exists cs', (c, s) --> cs') \/ (~(exists cs', (c, s) --> cs') /\ c = Skip).
Proof.
  induction c; sauto.
  - pose @SeqSemS2; scrush.
  - destruct (bval s b) eqn:?; pose @IfTrueS; pose @IfFalseS; scrush.
Qed.

Lemma lem_nonfinal_dec : forall cs, (exists cs', cs --> cs') \/ ~(exists cs', cs --> cs').
Proof.
  pose lem_nonfinal_dec_0; scrush.
Qed.

Lemma lem_finalD : forall c s, final (c, s) -> c = Skip.
Proof.
  Reconstr.hblast Reconstr.Empty
		  (@lem_nonfinal_dec_0)
		  (@final).
Qed.

Lemma lem_final_iff_SKIP : forall c s, final (c, s) <-> c = Skip.
Proof.
  split.
  - pose lem_finalD; scrush.
  - unfold final; scrush.
Qed.

Lemma lem_big_iff_small_termination :
  forall cs, (exists s, cs => s) <-> (exists cs', cs -->* cs' /\ final cs').
Proof.
  split.
  - pose cor_big_iff_small; pose lem_final_iff_SKIP; scrush.
  - intro H; destruct H as [cs']; destruct cs'.
    pose cor_big_iff_small; pose lem_final_iff_SKIP; scrush.
Qed.
