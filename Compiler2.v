Require Import Com.
Require Import Big_Step.
Require Import Star.
Require Import Compiler.
Require Import List String.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import ListNotations.

Fixpoint exec_n (l: list instr) (c1: config) (n: nat) (c2: config): Prop :=
  match n with
    | O   => c1 = c2
    | S m => exists c', (exec1 l c1 c') /\ (exec_n l c' m c2)
  end.

Definition isuccs (i: instr) (n: Z): list Z  :=
  match i with
    | JMP j     => [n + 1 + j]
    | JMPLESS j => [n + 1 + j; n + 1]
    | JMPGE j   => [n + 1 + j; n + 1]
    | _         => [n + 1]
  end.

Definition IsSucc (P : list instr) (n : Z) (s : Z) : Prop :=
  exists i, 0 <= i /\ i < size P /\ List.In s (isuccs (znth i P ADD) (n+i)).

Definition IsExit (P : list instr) (s : Z) : Prop :=
  IsSucc P 0 s /\ ~(0 <= s /\ s < size P).

Section BP_term_exec_n.

Lemma exec_n_exec: forall n P c1 c2,
    exec_n P c1 n c2 -> exec P c1 c2.
Proof.
  induction n; pose @star_step; ycrush.
Qed.

Lemma exec_0: forall P c, exec_n P c 0 c.
Proof. scrush. Qed.

Lemma exec_Suc: forall n P c1 c2 c3, exec1 P c1 c2 -> exec_n P c2 n c3 -> exec_n P c1 (S n) c3.
Proof. scrush. Qed.

Lemma exec_exec_n: forall P c1 c2,
    exec P c1 c2 ->exists n, exec_n P c1 n c2.
Proof.
  intros P c1 c2 H; induction H.
  - exists O; scrush. 
  - pose exec_Suc; scrush.
Qed.

Lemma exec_eq_exec_n: forall P c1 c2, 
    exec P c1 c2 <-> exists n, exec_n P c1 n c2.
Proof.
  pose exec_exec_n; pose exec_n_exec; scrush.
Qed.

Lemma exec_n_Nil: forall k c1 c2, exec_n [] c1 k c2 <-> (c1 = c2 /\ k = O).
Proof.
  induction k; sauto.
Qed.

Lemma exec1_exec_n: forall P c1 c2, exec1 P c1 c2 <-> exec_n P c1 1 c2.
Proof. scrush. Qed.

Lemma exec1_exec: forall P c1 c2, exec1 P c1 c2 -> exec P c1 c2.
Proof.
  intros.
  apply exec_n_exec with (n := 1%nat).
  apply exec1_exec_n.
  auto.
Qed.

Lemma exec_n_step: forall k n n' P s s' stk stk',
  n <> n' -> 
  exec_n P (n, stk, s) k (n', stk', s') <->
  exists c, exec1 P (n, stk, s) c /\ exec_n P c (k - 1) (n', stk', s') /\ Nat.lt 0%nat k.
Proof.
  destruct k.
  - sauto.
  - unfold exec_n; fold exec_n; split; intro; simp_hyps.
    + assert (HH: (S k - 1)%nat = k) by omega.
      rewrite HH; clear HH.
      exists c'.
      eauto with arith.
    + assert (HH: (S k - 1)%nat = k) by omega.
      rewrite HH in *; clear HH.
      exists c; auto.
Qed.

Lemma exec1_end: forall P c1 c2, size P <= (fst (fst c1)) -> ~(exec1 P c1 c2).
Proof.
  Reconstr.hobvious Reconstr.AllHyps
		    (@Coq.ZArith.BinInt.Z.lt_nge)
		    (@Coq.ZArith.BinInt.Z.lt).
Qed.

Lemma exec_n_end: forall k n n' P s s' stk stk',
  size P <= n -> exec_n P (n, s, stk) k (n', s', stk') -> (n' = n /\ stk' = stk /\ s' = s /\ k = 0%nat).
Proof.
  destruct k.
  - sauto.
  - unfold exec_n; fold exec_n; intros; simp_hyps.
    exfalso; apply exec1_end with (P := P) (c1 := (n, s, stk)) (c2 := c'); scrush.
Qed.

End BP_term_exec_n.

Section BP_term_succs.

Lemma succs_simps: forall n v x i,
    (forall s, IsSucc [ADD] n s <-> s = n + 1) /\
    (forall s, IsSucc [LOADI v] n s <-> s = n + 1) /\
    (forall s, IsSucc [LOAD x] n s <-> s = n + 1) /\
    (forall s, IsSucc [STORE x] n s <-> s = n + 1) /\
    (forall s, IsSucc [JMP i] n s <-> s = n + 1 + i) /\
    (forall s, IsSucc [JMPGE i] n s <-> s = n + 1 + i \/ s = n + 1) /\
    (forall s, IsSucc [JMPLESS i] n s <-> s = n + 1 + i \/ s = n + 1).
Proof.
  unfold IsSucc.
  intros; repeat split; intro; simp_hyps; cbn in *;
    solve [ assert (i0 = 0) by omega; sauto | exists 0; sauto ].
Qed.

Lemma succs_empty: forall n s, ~(IsSucc [] n s).
Proof.
  unfold IsSucc.
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.le_refl, @Coq.ZArith.BinInt.Z.abs_eq,
                     @Coq.ZArith.BinInt.Z.ltb_nlt, @Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.BinInt.Z.le_lt_trans)
		    (@Compiler.size).
Qed.

Lemma succs_Cons: forall x xs n s,
    IsSucc (x :: xs) n s <-> List.In s (isuccs x n) \/ IsSucc xs (n + 1) s.
Proof.
  split; intro H; unfold IsSucc in H; simp_hyps.
  - assert (H2: i = 0 \/ i > 0) by
	Reconstr.hcrush (@H)
		(@Coq.ZArith.BinInt.Z.lt_eq_cases, @Coq.ZArith.BinInt.Z.lt_nge, @Coq.ZArith.Zorder.Znot_le_gt)
		Reconstr.Empty.
    assert (H3: i = 0 \/ exists j, j >= 0 /\ i = j + 1) by
    (sauto; [
       Reconstr.hcrush Reconstr.AllHyps
		    (@Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.Znat.Z2Nat.id, @Coq.ZArith.Znat.Z2Nat.inj_0)
		    (@Coq.ZArith.BinIntDef.Z.abs) |
       Reconstr.hcrush Reconstr.AllHyps
		       (@Coq.ZArith.BinInt.Z.le_exists_sub, @Coq.ZArith.BinInt.Z.le_gt_cases, @Coq.ZArith.BinInt.Z.add_0_l, @Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.BinInt.Z.ge_le_iff)
		       (@Coq.ZArith.BinInt.Z.lt) ]).
    clear H2.
    destruct H3; simp_hyps.
    + sauto.
    + subst; right; unfold IsSucc.
      exists j.
      repeat split.
      * auto with zarith.
      * Reconstr.hsimple Reconstr.AllHyps
		         (@Coq.ZArith.BinInt.Z.add_lt_mono_r, @Compiler.lem_size_succ)
		         Reconstr.Empty.
      * Reconstr.hcrush Reconstr.AllHyps
		        (@Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.ge_le_iff,
                         @Coq.ZArith.BinInt.Zplus_assoc_reverse, @Compiler.lem_n_succ_znth)
		        Reconstr.Empty.
  - destruct H.
    + unfold IsSucc; exists 0; scrush.
    + unfold IsSucc; simp_hyps. exists (i + 1).
      repeat split.
      * omega.
      * Reconstr.hcrush Reconstr.AllHyps
		        (@Coq.ZArith.BinInt.Z.add_lt_mono_r, @Compiler.lem_size_succ)
		        Reconstr.Empty.
      * sauto; [
          Reconstr.hcrush Reconstr.AllHyps
		          (@Coq.ZArith.Znat.Z2Nat.inj_succ)
		          (@Coq.ZArith.BinIntDef.Z.succ) |
	  Reconstr.hcrush Reconstr.AllHyps
		          (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.Znat.Z2Nat.inj_succ, @Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_shuffle3)
		          (@Compiler.znth, @Coq.ZArith.BinIntDef.Z.succ) ].
Qed.

Lemma succs_iexec1: forall P n s stk c,
    0 <= n -> n < size P -> c = iexec (znth n P ADD) (n, s, stk) -> IsSucc P 0 (fst (fst c)).
Proof.
  unfold IsSucc; unfold iexec.
  sauto; exists n; scrush.
Qed.

End BP_term_succs.
