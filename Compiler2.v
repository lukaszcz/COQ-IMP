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
                          (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_comm,
               @Coq.ZArith.Znat.Z2Nat.inj_succ, @Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_shuffle3)
                          (@Compiler.znth, @Coq.ZArith.BinIntDef.Z.succ) ].
Qed.

Lemma succs_iexec1: forall P n s stk c,
    0 <= n -> n < size P -> c = iexec (znth n P ADD) (n, s, stk) -> IsSucc P 0 (fst (fst c)).
Proof.
  unfold IsSucc; unfold iexec.
  sauto; exists n; scrush.
Qed.

Lemma In_help: forall p n x, In (p - n) [x + 1] <-> In p [n + x + 1].
Proof. split; intros; unfold In in *.
       destruct H. left.
        Reconstr.heasy (@AllHyps)
                   (@Coq.ZArith.BinInt.Z.add_0_r, @Coq.ZArith.BinInt.Z.add_comm,
        @Coq.ZArith.BinInt.Z.sub_add_simpl_r_l, @Coq.ZArith.BinInt.Z.add_succ_l)
                   (@Coq.ZArith.BinIntDef.Z.succ).
       scrush.
       destruct H. left.
             Reconstr.heasy (@AllHyps)
                   (@Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_0_r,
        @Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.add_assoc,
        @Coq.ZArith.BinInt.Z.add_opp_r, @Coq.ZArith.BinInt.Z.sub_add_simpl_r_l, @Coq.ZArith.BinInt.Z.add_0_l)
                   (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).
       scrush.
Qed.

Lemma succs_shift: forall n p P, IsSucc P 0 (p - n) <-> IsSucc P n p.
Proof. split; intros; unfold IsSucc, isuccs.
       destruct H. exists x.
       destruct H, H0.
       split. easy.
       split. easy. cbn in *.
       case_eq (znth x P ADD); intros; unfold isuccs in *; rewrite H2 in *; try  now apply In_help.
       specialize (In_help p n (x + z)); intros.
       assert (n + (x + z) + 1 = n + x + 1 + z) by
              Reconstr.htrivial Reconstr.Empty
                   (@Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_assoc)
                   (@Coq.ZArith.BinIntDef.Z.succ); subst;
       assert (x + z + 1 = x + 1 + z) by
         Reconstr.htrivial Reconstr.Empty
                    (@Coq.ZArith.BinInt.Z.add_succ_l)
                    (@Coq.ZArith.BinIntDef.Z.succ); subst.
       (scrush;
       unfold In in *;
       destruct H1; left; omega;
       destruct H1; right; left; omega;
       scrush).
       unfold In in *;
	     Reconstr.htrivial (@H1)
		      (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      (@Coq.ZArith.BinIntDef.Z.sub).
       unfold In in *;
	     Reconstr.htrivial (@H1)
		      (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      (@Coq.ZArith.BinIntDef.Z.sub).
       unfold IsSucc, isuccs in H. destruct H.
       exists x;
       split; try easy; split; try easy.

       destruct H, H0; cbn in *;
       case_eq (znth x P ADD); intros; rewrite H2 in *; try now apply In_help.
	     Reconstr.hcrush (@H1)
		      (@BP_term_succs.In_help, @Coq.ZArith.BinInt.Z.add_succ_r, 
           @Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_comm, 
           @Coq.ZArith.BinInt.Zplus_assoc_reverse)
		      (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).

       unfold In in H1; destruct H1;
	     Reconstr.hblast (@H1)
		      (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_simpl_l)
		      (@Coq.ZArith.BinIntDef.Z.sub).
	     Reconstr.hblast (@H1)
		      (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_simpl_l)
		      (@Coq.ZArith.BinIntDef.Z.sub).
Qed.

Lemma helper: forall y n, n + 1 + Z.of_nat y = n + Z.of_nat (1 + y).
Proof. intro n; induction n; sauto;
	     Reconstr.htrivial (@IHn)
		      (@Coq.ZArith.BinInt.Z.add_succ_comm, @Coq.ZArith.BinInt.Z.opp_0, 
           @Coq.ZArith.BinInt.Z.add_0_l, @Coq.ZArith.BinInt.Z.opp_add_distr, 
           @Coq.ZArith.BinInt.Pos2Z.inj_succ)
		      (@Coq.ZArith.BinIntDef.Z.opp, @Coq.ZArith.BinIntDef.Z.succ); scrush.
Qed.

Lemma succs_append_l: forall xs ys n s, IsSucc (xs ++ ys) n s -> IsSucc xs n s \/ IsSucc ys (n + size xs) s.
Proof. intro xs; induction xs; intros.
       - cbn in *; assert (n + 0 = n) by scrush; scrush.
       - intros. cbn in H. apply succs_Cons in H.
         destruct H.
	       Reconstr.htrivial (@H)
		        (@BP_term_succs.succs_Cons)
		        Reconstr.Empty; scrush.
         specialize (IHxs ys (n + 1) s H).
	       Reconstr.hblast (@IHxs)
		        (@Compiler.lem_size_succ, @Coq.ZArith.BinInt.Z.add_succ_l,
             @Coq.ZArith.BinInt.Z.add_comm, @BP_term_succs.succs_Cons)
		        (@Coq.ZArith.BinIntDef.Z.succ).
Qed.

Lemma succs_append_r: forall xs ys n s, IsSucc xs n s \/ IsSucc ys (n + size xs) s -> IsSucc (xs ++ ys) n s.
Proof. intro xs; induction xs; intros.
       - 	Reconstr.hobvious (@H)
		      (@BP_term_succs.succs_empty, @Coq.ZArith.BinInt.Z.add_0_l, 
           @Coq.ZArith.BinInt.Z.add_cancel_r, @Coq.Lists.List.app_nil_l, 
           @Compiler.lem_size_app, @Coq.ZArith.BinInt.Zplus_0_r_reverse)
		      Reconstr.Empty.
       - destruct H. apply succs_Cons in H;
         cbn; apply succs_Cons; destruct H; scrush.
         cbn; apply succs_Cons; right; apply IHxs; unfold size;
	       Reconstr.hblast (@H)
		        (@Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.add_succ_l, @Compiler.lem_size_succ)
		        (@Coq.ZArith.BinIntDef.Z.succ, @Compiler.size).
Qed.


Lemma succs_append: forall xs ys n s, IsSucc (xs ++ ys) n s <-> IsSucc xs n s \/ IsSucc ys (n + size xs) s.
Proof. pose succs_append_l; pose succs_append_r; scrush. Qed.

Lemma succs_set_shift:
  forall xs i s, IsSucc xs 0 s <-> IsSucc xs i (s + i).
Proof.
  intros xs i s; split; intro H.
  - apply succs_shift with (n := i).
    Reconstr.hobvious (@H)
                      (@Coq.ZArith.BinInt.Z.add_simpl_r)
                      (@Coq.ZArith.BinIntDef.Z.sub).
  - assert (HH: s = (s + i) - i) by omega.
	  Reconstr.hobvious (@H, @HH)
	  	(@BP_term_succs.succs_shift)
		  Reconstr.Empty.
Qed.

Lemma exits_append : forall xs ys s,
    IsExit (xs ++ ys) s <-> (IsExit xs s \/ IsExit ys (s - size xs)) /\ ~(0 <= s /\ s < size xs + size ys).
Proof.
  unfold IsExit.
  intros xs ys s.
  rewrite lem_size_app.
  split; intro H.
  - assert (Hsize0: forall l, 0 <= size l) by
        Reconstr.hobvious Reconstr.Empty
                          (@Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.Zorder.Zle_0_nat)
                          (@Coq.ZArith.BinInt.Z.lt, @Coq.ZArith.BinInt.Z.ge, @Compiler.size).
    assert (Hn1: forall n m k, 0 <= m -> n < k -> n < k + m) by (intros; omega).
    assert (Hn2: forall n m k, n < k + m -> n - k < m) by (intros; omega).
    assert (Hn3: forall n m, 0 <= m -> 0 <= n - m -> 0 <= n) by (intros; omega).
    assert (~(0 <= s < size xs)) by scrush.
    assert (~(0 <= s - size xs < size ys)) by
        Reconstr.hobvious (@Hsize0, @Hn3, @H)
                          (@Coq.ZArith.BinInt.Z.lt_sub_lt_add_l)
                          (@Coq.ZArith.BinIntDef.Z.sub).
    Reconstr.hobvious Reconstr.AllHyps
                      (@Coq.ZArith.BinInt.Z.add_0_l, @BP_term_succs.succs_append_l, @BP_term_succs.succs_shift)
                      Reconstr.Empty.
  - split.
    + destruct H as [H H0].
      destruct H.
      * Reconstr.heasy (@H)
                       (@BP_term_succs.succs_append_r)
                       Reconstr.Empty.
      * Reconstr.heasy (@H)
                       (@Coq.ZArith.BinInt.Z.add_0_l, @BP_term_succs.succs_shift,
                        @BP_term_succs.succs_append_r)
                       Reconstr.Empty.
    + scrush.
Qed.

Lemma exits_single_l: forall x s, IsExit [x] s -> List.In s (isuccs x 0) /\ s <> 0.
Proof. unfold IsExit, IsSucc.
       sauto;
         solve [
             pose Coq.ZArith.BinInt.Z.lt_eq_cases; pose Coq.ZArith.Znat.Z2Nat.inj_0;
             rewrite Coq.ZArith.Znat.Z2Nat.inj with (n := 0) (m := i); scrush |
             Reconstr.heasy Reconstr.AllHyps
                            (@Coq.ZArith.Znat.Z2Nat.inj, @Coq.ZArith.Znat.Z2Nat.inj_0,
                             @Coq.ZArith.BinInt.Z.lt_eq_cases)
                            (@Coq.ZArith.BinInt.Z.lt) ].
Qed.

Lemma exits_single_r: forall x s, List.In s (isuccs x 0) /\ s <> 0 -> IsExit [x] s.
Proof. unfold IsExit, IsSucc; sauto.
	Reconstr.hobvious (@H0)
		(@Coq.ZArith.BinInt.Z.lt_0_1, @Coq.ZArith.BinInt.Z.le_refl, @Coq.ZArith.Znat.Z2Nat.inj_0)
		Reconstr.Empty.
	Reconstr.hcrush (@H2, @H1, @H4)
		(@Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.BinInt.Z.compare_eq_iff, 
     @Coq.ZArith.BinInt.Z.compare_lt_iff, @Coq.ZArith.BinInt.Z.compare_eq,
     @Coq.ZArith.BinInt.Z.lt_eq_cases, @Coq.ZArith.BinInt.Z.add_0_r, 
     @Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.Zcompare.Zcompare_Gt_Lt_antisym)
		Reconstr.Empty.
Qed.

Lemma exits_single: forall x s, IsExit [x] s <-> List.In s (isuccs x 0) /\ s <> 0.
Proof. pose exits_single_l; pose exits_single_r; scrush. Qed.

Lemma exits_Cons: forall x xs s,
    IsExit (x :: xs) s <-> ((List.In s (isuccs x 0) /\ s <> 0) \/ IsExit xs (s - 1)) /\ ~(0 <= s < 1 + size xs).
Proof.
  intros x xs s.
  rewrite <- exits_single.
  split; intro; apply exits_append with (xs := [x]); scrush.
Qed.

Lemma exits_empty: forall s, IsExit [] s <-> List.In s [].
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@BP_term_succs.succs_empty, @Coq.Lists.List.in_nil)
		(@IsExit).
Qed.

Lemma exits_simps: forall v x i s,
  (IsExit [ADD] s <-> s = 1) /\
  (IsExit [LOADI v] s <-> s = 1) /\
  (IsExit [LOAD x] s <-> s = 1) /\
  (IsExit [STORE x] s <-> s = 1) /\
  (i <> -1 -> IsExit [JMP i] s <-> s = 1 + i) /\
  (i <> -1 -> IsExit [JMPGE i] s <-> s = 1 + i \/ s = 1) /\
  (i <> -1 -> IsExit [JMPLESS i] s <-> s = 1 + i \/ s = 1).
Proof.
  unfold IsExit; unfold IsSucc; unfold isuccs.
  assert (forall i, (i ?= 1) = Lt -> 0 <= i -> i + 1 = 1) by
      (clear; intros; assert (i < 1) by scrush; omega).
  assert (forall i, (i ?= 1) = Lt -> 0 <= i -> i = 0) by
      (clear; intros; assert (i < 1) by scrush; omega).
  sauto; try exists 0; scrush. (* 11s *)
Qed.

End BP_term_succs.

Lemma lem_acomp_succs_hlp1: forall l, znth (size l) (l ++ [ADD]) ADD = ADD.
Proof.
  induction l; sauto.
  - Reconstr.htrivial (@Heqn)
                      (@Coq.Arith.PeanoNat.Nat.sub_1_r, @Coq.Arith.PeanoNat.Nat.neq_succ_0, @Coq.Arith.PeanoNat.Nat.le_0_r, @Coq.Arith.PeanoNat.Nat.sub_0_le, @Coq.PArith.Pnat.Pos2Nat.inj_1, @Coq.PArith.Pnat.SuccNat2Pos.id_succ, @Coq.PArith.Pnat.SuccNat2Pos.pred_id, @Coq.Init.Peano.le_S)
                      Reconstr.Empty.
  - unfold size in *; unfold znth in *.
    assert (Z.to_nat (Z.of_nat (Datatypes.length l)) = n) by
        Reconstr.hobvious (@Heqn)
                          (@Coq.Arith.PeanoNat.Nat.pred_succ, @Coq.PArith.Pnat.SuccNat2Pos.id_succ, @Coq.ZArith.Znat.Nat2Z.id)
                          Reconstr.Empty.
    scrush.
Qed.

Ltac acomp_succs_blast_tac :=
  match goal with
    [ H: 0 <= ?x, H2: (?x ?= 1) = Lt |- _ ] =>
    Reconstr.hblast (@H2, @H)
                    (@Coq.ZArith.BinInt.Z.succ_le_mono, @Coq.ZArith.BinInt.Z.add_comm,
                     @Coq.ZArith.BinInt.Z.one_succ, @Coq.ZArith.BinInt.Z.le_antisymm,
                     @Coq.ZArith.BinInt.Z.succ_m1, @Coq.ZArith.BinInt.Z.add_succ_r,
                     @Coq.ZArith.BinInt.Z.add_1_l, @Coq.ZArith.BinInt.Z.add_0_l,
                     @Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.BinInt.Z.le_refl)
                    (@Coq.ZArith.BinIntDef.Z.succ, @Coq.ZArith.BinInt.Z.le)
  end.

Ltac ex_omega_tac := unfold IsSucc; unfold isuccs; exists 0; sauto; omega.

Lemma acomp_succs:
  forall a n s, IsSucc (acomp a) n s <-> n + 1 <= s <= n + size (acomp a).
Proof.
  induction a; sauto; try omega; try acomp_succs_blast_tac. (* 3s *)
  - ex_omega_tac.
  - ex_omega_tac.
  - assert (IsSucc (acomp a1 ++ acomp a2 ++ [ADD]) n s) by (unfold IsSucc; scrush).
    assert (IsSucc (acomp a1) n s \/ IsSucc (acomp a2) (n + size (acomp a1)) s \/
            IsSucc [ADD] (n + size (acomp a1) + size (acomp a2)) s) by
        (assert (IsSucc (acomp a1) n s \/ IsSucc (acomp a2 ++ [ADD]) (n + size (acomp a1)) s) by
            (apply succs_append; scrush);
         pose succs_append; scrush).
    assert (forall l, 0 <= size l) by
        Reconstr.hobvious Reconstr.Empty
                          (@Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.Zorder.Zle_0_nat)
                          (@Coq.ZArith.BinInt.Z.lt, @Coq.ZArith.BinInt.Z.ge, @Compiler.size).
    intuition.
    + assert (n + size (acomp a1) + 1 <= s) by scrush.
      assert (0 <= size (acomp a1)) by scrush.
      omega.
    + unfold IsSucc in H8.
      simp_hyps.
      assert (HH: i = 0) by
          (unfold size in *; simpl in *; omega).
      rewrite HH in *; clear HH.
      sauto.
      assert (0 <= size (acomp a1)) by scrush.
      assert (0 <= size (acomp a2)) by scrush.
      omega.
  - assert (IsSucc (acomp a1 ++ acomp a2 ++ [ADD]) n s) by (unfold IsSucc; scrush).
    assert (IsSucc (acomp a1) n s \/ IsSucc (acomp a2) (n + size (acomp a1)) s \/
            IsSucc [ADD] (n + size (acomp a1) + size (acomp a2)) s) by
        (assert (IsSucc (acomp a1) n s \/ IsSucc (acomp a2 ++ [ADD]) (n + size (acomp a1)) s) by
            (apply succs_append; scrush);
         pose succs_append; scrush).
    assert (forall l, 0 <= size l) by
        Reconstr.hobvious Reconstr.Empty
                          (@Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.Zorder.Zle_0_nat)
                          (@Coq.ZArith.BinInt.Z.lt, @Coq.ZArith.BinInt.Z.ge, @Compiler.size).
    repeat rewrite lem_size_app.
    assert (0 <= size (acomp a2)) by scrush.
    assert (HH: size [ADD] = 1) by scrush.
    rewrite HH; clear HH.
    intuition.
    + assert (s <= n + size (acomp a1)) by scrush.
      omega.
    + assert (s <= n + size (acomp a1) + size (acomp a2)) by scrush.
      omega.
    + unfold IsSucc in H8.
      simp_hyps.
      assert (HH: i = 0) by
          (unfold size in *; simpl in *; omega).
      rewrite HH in *; clear HH.
      sauto.
      omega.
  - repeat rewrite lem_size_app in *.
    assert (forall l, 0 <= size l) by
        Reconstr.hobvious Reconstr.Empty
                          (@Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.Zorder.Zle_0_nat)
                          (@Coq.ZArith.BinInt.Z.lt, @Coq.ZArith.BinInt.Z.ge, @Compiler.size).
    assert (0 <= size (acomp a2)) by scrush.
    assert (HH: size [ADD] = 1) by scrush.
    rewrite HH in *; clear HH.
    assert (HH: s <= n + size (acomp a1) + size (acomp a2) \/
                s = n + size (acomp a1) + size (acomp a2) + 1) by omega.
    destruct HH.
    + assert (HH: n + size (acomp a1) + 1 <= s \/ s <= n + size (acomp a1)) by omega.
      destruct HH.
      * assert (IsSucc (acomp a2) (n + size (acomp a1)) s) by scrush.
        pose succs_append; scrush.
      * assert (IsSucc (acomp a1) n s) by scrush.
        pose succs_append; scrush.
    + subst.
      unfold IsSucc; unfold isuccs.
      repeat rewrite lem_size_app.
      exists (size (acomp a1) + size (acomp a2)).
      assert (HH: size [ADD] = 1) by scrush.
      rewrite HH; clear HH.
      repeat split; simpl; try omega.
      assert (HH: znth (size (acomp a1) + size (acomp a2)) (acomp a1 ++ acomp a2 ++ [ADD]) ADD = ADD) by
          (rewrite <- lem_size_app; rewrite List.app_assoc; rewrite lem_acomp_succs_hlp1; trivial).
      rewrite HH; clear HH.
      Reconstr.hobvious Reconstr.Empty
                        (@Coq.Lists.List.not_in_cons, @Coq.ZArith.BinInt.Zplus_assoc_reverse)
                        (@Coq.ZArith.BinIntDef.Z.succ).
Qed.

Lemma acomp_size : forall a, 1 <= size (acomp a).
Proof.
  induction a; sauto.
  repeat rewrite lem_size_app.
  assert (size [ADD] = 1) by scrush.
  omega.
Qed.

Lemma acomp_exits : forall a s, IsExit (acomp a) s <-> s = size (acomp a).
Proof.
  unfold IsExit; intros a s; split; intro H.
  - Reconstr.hcrush (@H)
                    (acomp_succs, @Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.BinInt.Z.nle_gt,
                     @Coq.ZArith.BinInt.Z.gt_lt_iff, @Coq.ZArith.BinInt.Z.lt_eq_cases,
                     @Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.add_0_r,
                     @Coq.ZArith.BinInt.Z.le_exists_sub, @Coq.ZArith.Zorder.Zle_0_nat,
                     @Coq.ZArith.BinInt.Z.one_succ)
                    (@Coq.ZArith.BinInt.Z.gt, @Coq.ZArith.BinInt.Z.le, @Compiler.size,
                     @Coq.ZArith.BinIntDef.Z.succ).
  - Reconstr.hobvious (@H)
                      (@Coq.ZArith.BinInt.Z.add_0_r, @Coq.ZArith.BinInt.Z.add_comm,
                       @Coq.ZArith.BinInt.Z.le_refl, @Coq.ZArith.BinInt.Z.nle_gt,
                       @acomp_size, @acomp_succs, @Coq.ZArith.BinInt.Z.one_succ)
                      (@Coq.ZArith.BinIntDef.Z.succ).
Qed.

Lemma bcomp_succs :
  forall b f i n, 0 <= i -> forall s,
      IsSucc (bcomp b f i) n s ->
      n <= s <= n + size (bcomp b f i) \/ s = n + i + size (bcomp b f i).
Proof.
  induction b; sauto.
  - Reconstr.hblast (@H3, @H0)
                    (@Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.add_0_l, @Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.BinInt.Z.add_0_r)
                  (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinIntDef.Z.succ).
  - Reconstr.hblast (@H0, @H3, @Heqn0)
                  (@Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.add_0_l, @Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.Znat.Z2Nat.inj_0)
                  (@Coq.ZArith.BinInt.Z.le).
  - assert (x = 0) by
        Reconstr.hblast (@H0, @H3)
                        (@Coq.ZArith.BinInt.Z.compare_eq_iff, @Coq.ZArith.BinInt.Z.compare_lt_iff, @Coq.ZArith.BinInt.Z.compare_nge_iff, @Coq.ZArith.BinInt.Z.le_succ_l, @Coq.ZArith.BinInt.Z.one_succ)
                        (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinIntDef.Z.min).
    scrush.
  - Reconstr.hobvious (@H0, @H3)
                      (@Coq.ZArith.BinInt.Z.ge_le_iff)
                      (@Coq.ZArith.BinInt.Z.ge).
  - Reconstr.hobvious (@H3, @H0)
                      (@Coq.ZArith.BinInt.Z.lt_nge)
                      (@Coq.ZArith.BinInt.Z.lt).
  - assert (IsSucc (bcomp b1 false (size (bcomp b2 true i)) ++ bcomp b2 true i) n s) by
        (unfold IsSucc; scrush).
    assert (H3: IsSucc (bcomp b1 false (size (bcomp b2 true i))) n s \/
            IsSucc (bcomp b2 true i) (n + size (bcomp b1 false (size (bcomp b2 true i)))) s) by
        (pose succs_append_l; scrush).
    repeat rewrite lem_size_app.
    destruct H3.
    + clear -H3 IHb1.
      assert (H: 0 <= size (bcomp b2 true i)) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      specialize (IHb1 false (size (bcomp b2 true i)) n H s H3).
      assert (0 <= size (bcomp b1 false (size (bcomp b2 true i)))) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
    + clear -H H3 IHb2.
      specialize (IHb2 true i (n + size (bcomp b1 false (size (bcomp b2 true i)))) H s H3).
      assert (0 <= size (bcomp b1 false (size (bcomp b2 true i)))) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
  - assert (IsSucc (bcomp b1 false (size (bcomp b2 false i) + i) ++ bcomp b2 false i) n s) by
        (unfold IsSucc; scrush).
    assert (H3: IsSucc (bcomp b1 false (size (bcomp b2 false i) + i)) n s \/
            IsSucc (bcomp b2 false i) (n + size (bcomp b1 false (size (bcomp b2 false i) + i))) s) by
        (pose succs_append_l; scrush).
    repeat rewrite lem_size_app.
    destruct H3.
    + clear -H H3 IHb1.
      assert (H0: 0 <= size (bcomp b2 false i)) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      assert (H1: 0 <= size (bcomp b2 false i) + i) by omega.
      specialize (IHb1 false (size (bcomp b2 false i) + i) n H1 s H3).
      assert (0 <= size (bcomp b1 false (size (bcomp b2 false i) + i))) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
    + clear -H H3 IHb2.
      specialize (IHb2 false i (n + size (bcomp b1 false (size (bcomp b2 false i) + i))) H s H3).
      assert (0 <= size (bcomp b1 false (size (bcomp b2 false i) + i))) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
  - assert (IsSucc (acomp a ++ acomp a0 ++ [JMPLESS i]) n s) by (unfold IsSucc; scrush).
    assert (H3: IsSucc (acomp a) n s \/ IsSucc (acomp a0 ++ [JMPLESS i]) (n + size (acomp a)) s) by
        (pose succs_append_l; scrush).
    repeat rewrite lem_size_app.
    destruct H3.
    + assert (n + 1 <= s <= n + size (acomp a)) by (apply acomp_succs; scrush).
      assert (0 <= size (acomp a0)) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      assert (0 <= size [JMPLESS i]) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
    + assert (HH: IsSucc (acomp a0) (n + size (acomp a)) s \/
                  IsSucc [JMPLESS i] (n + size (acomp a) + size (acomp a0)) s) by
          (pose succs_append_l; scrush).
      destruct HH.
      * assert (n + size (acomp a) + 1 <= s <= n + size (acomp a) + size (acomp a0)) by
            (apply acomp_succs; scrush).
        assert (0 <= size (acomp a)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        assert (0 <= size [JMPLESS i]) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        omega.
      * assert (H6: s = n + size (acomp a) + size (acomp a0) + 1 + i \/
                    s = n + size (acomp a) + size (acomp a0) + 1) by (apply succs_simps; scrush).
        assert (HH: size [JMPLESS i] = 1) by scrush.
        repeat rewrite HH; clear HH.
        assert (0 <= size (acomp a)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        assert (0 <= size (acomp a0)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        omega.
  - assert (IsSucc (acomp a ++ acomp a0 ++ [JMPGE i]) n s) by (unfold IsSucc; scrush).
    assert (H3: IsSucc (acomp a) n s \/ IsSucc (acomp a0 ++ [JMPGE i]) (n + size (acomp a)) s) by
        (pose succs_append_l; scrush).
    repeat rewrite lem_size_app.
    destruct H3.
    + assert (n + 1 <= s <= n + size (acomp a)) by (apply acomp_succs; scrush).
      assert (0 <= size (acomp a0)) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      assert (0 <= size [JMPGE i]) by
          Reconstr.htrivial Reconstr.Empty
                            (@Coq.ZArith.Zorder.Zle_0_nat)
                            (@Compiler.size).
      omega.
    + assert (HH: IsSucc (acomp a0) (n + size (acomp a)) s \/
                  IsSucc [JMPGE i] (n + size (acomp a) + size (acomp a0)) s) by
          (pose succs_append_l; scrush).
      destruct HH.
      * assert (n + size (acomp a) + 1 <= s <= n + size (acomp a) + size (acomp a0)) by
            (apply acomp_succs; scrush).
        assert (0 <= size (acomp a)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        assert (0 <= size [JMPGE i]) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        omega.
      * assert (H6: s = n + size (acomp a) + size (acomp a0) + 1 + i \/
                    s = n + size (acomp a) + size (acomp a0) + 1) by
            (pose succs_simps; simp_hyps; yelles 1%nat).
        assert (HH: size [JMPGE i] = 1) by scrush.
        repeat rewrite HH; clear HH.
        assert (0 <= size (acomp a)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        assert (0 <= size (acomp a0)) by
            Reconstr.htrivial Reconstr.Empty
                              (@Coq.ZArith.Zorder.Zle_0_nat)
                              (@Compiler.size).
        omega.
Qed.

Lemma bcomp_exits:
  forall b f i, 0 <= i -> forall s,
      IsExit (bcomp b f i) s ->
      s = size (bcomp b f i) \/ s <= i + size (bcomp b f i).
Proof.  unfold IsExit; intros; unfold size in *;
       destruct H0; apply bcomp_succs in H0; destruct H0; cbn in *;
       sauto; unfold size in *;
	     Reconstr.hobvious (@H3, @H2)
		      (@Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.lt_ge_cases)
		      (@Compiler.size).
Qed.

Lemma bcomp_existsD: 
  forall b f i, 0 <= i -> forall s, exists s',
      IsExit (bcomp b f i) s ->
      s' = size (bcomp b f i) \/ s' <= i + size (bcomp b f i).
Proof. scrush. Qed.

Lemma size_app: forall l m, size (l ++ m) = size l + size m.
Proof. 	
    Reconstr.htrivial Reconstr.Empty
		 (@Compiler.lem_size_app)
		 Reconstr.Empty.
Qed.

Lemma ccomp_size: forall c, size (ccomp c) >= 0.
Proof. 
	Reconstr.hobvious Reconstr.Empty
		(@Coq.ZArith.BinInt.Z.ge_le_iff, @Coq.ZArith.Zorder.Zle_0_nat)
		(@Coq.ZArith.BinInt.Z.ge, @Compiler.size).
Qed.

Lemma list_size: forall l, size l >= 0.
Proof. 
	Reconstr.hobvious Reconstr.Empty
		(@Coq.ZArith.Zorder.Zle_0_nat, @Coq.ZArith.BinInt.Z.ge_le_iff, @Coq.ZArith.Zeven.Zquot2_odd_eqn)
		(@Coq.ZArith.BinInt.Z.ge, @Compiler.size).
Qed.

Lemma ccomp_succs: 
  forall c i n, 0 <= i -> forall s,
      IsSucc (ccomp c) n s -> n <= s <= n + size (ccomp c).
Proof. intro c; induction c; intros.
       - sauto;
         Reconstr.hobvious (@H3, @H0)
		      (@Coq.ZArith.BinInt.Z.compare_ge_iff)
		      Reconstr.Empty.
       - cbn in *. specialize (succs_append (acomp a) [STORE v] n s); intros.
         apply H1 in H0. destruct H0.
         apply acomp_succs in H0. 
         assert (size (acomp a ++ [STORE v]) = size (acomp a) + 1) by
	        Reconstr.hobvious Reconstr.Empty
		        (@Coq.ZArith.auxiliary.Zegal_left, @Coq.Lists.List.app_nil_l, 
             @Compiler.lem_size_succ, @Coq.ZArith.BinInt.Z.add_simpl_r, 
             @Compiler.lem_size_app, @Coq.ZArith.BinInt.Z.one_succ)
		        (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).
	        Reconstr.hcrush (@H0, @H2)
		        (@Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.BinInt.Z.lt_eq_cases, 
             @Coq.ZArith.BinInt.Z.le_succ_l, @Coq.ZArith.BinInt.Z.add_succ_r)
		        (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinIntDef.Z.succ, @Coq.ZArith.BinInt.Z.lt).
         unfold IsSucc in *. destruct H0, H0, H2.
         assert (x = 0).  unfold size in H2. cbn in H2. 
         Reconstr.htrivial (@H0, @H2)
		      (@Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.BinInt.Z.le_antisymm, 
		       @Coq.ZArith.BinInt.Z.one_succ)
		       Reconstr.Empty.
		     rewrite H4 in *. cbn in *. 
		     destruct H3. subst. split. 
         assert (size (acomp a) >= 0) by apply list_size.
         omega. 
         rewrite size_app. cbn. omega.
		     easy.
		   - cbn in *.
		     specialize (succs_append (ccomp c1) (ccomp c2) n s); intros.
         apply H1 in H0. destruct H0. 
         specialize (IHc1 i n H s H0).
         case_eq (ccomp c2); intros; subst. scrush.
         unfold size. rewrite app_length. cbn.
         unfold size in IHc1.
         split. omega.
         assert (Z.of_nat (Datatypes.length (ccomp c1) + S (Datatypes.length l)) = 
         Z.of_nat (Datatypes.length (ccomp c1) + (Datatypes.length l) + 1)) by
	       Reconstr.htrivial Reconstr.Empty
		        (@Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Init.Peano.plus_n_Sm)
		        Reconstr.Empty.

         rewrite H3.
         rewrite !Nat2Z.inj_add. omega.
         specialize (IHc2 i (n + size (ccomp c1)) H s H0).
         rewrite size_app. split; try omega.
         pose acomp_size;
         destruct IHc2;
         specialize (ccomp_size c1); intros; omega.
       - cbn in *. apply succs_append in H0. destruct H0.
         apply bcomp_succs in H0. destruct H0.
         rewrite !size_app. cbn; split; try omega.
         destruct H0.
         specialize (ccomp_size c1); intros.
         specialize (ccomp_size c2); intros.
         rewrite !Z.add_assoc.
         assert ( Z.pos (Pos.of_succ_nat (Datatypes.length (ccomp c2))) >= 0) by scrush.
         omega. subst. cbn. split.
         rewrite Z.add_assoc.
         specialize (ccomp_size c1); intros.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0).
         apply list_size. omega.
         rewrite !size_app. unfold size.
         cbn. rewrite !Z.add_assoc. 
         rewrite Zpos_P_of_succ_nat. omega.
         remember (ccomp_size c1); intros. omega.
         apply succs_append in H0. destruct H0.
         specialize (IHc1 i (n + size (bcomp b false (size (ccomp c1) + 1))) H s H0).
         split. destruct IHc1.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0).
         apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat. omega.
         apply succs_Cons in H0.
         destruct H0. cbn in *.
         destruct H0. subst. split.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c1) >= 0) by apply list_size.
         assert (size (ccomp c2) >= 0) by apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat.
         unfold size in *. omega. easy.
         specialize (IHc2 i (n + size (bcomp b false (size (ccomp c1) + 1)) + size (ccomp c1) + 1) H s H0).
         destruct IHc2. split.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c1) >= 0) by apply list_size.
         assert (size (ccomp c2) >= 0) by apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat.
         unfold size in *. omega.
       - cbn in *. apply succs_append in H0. destruct H0.
         apply bcomp_succs in H0.  destruct H0.
         assert (Datatypes.length [JMP (- (size (bcomp b false (size (ccomp c) + 1)) +
                 size (ccomp c) + 1))] = 1%nat) by easy.
         split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size. omega.
         subst. split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn. omega.
         unfold size. omega.
         apply succs_append in H0. destruct H0.
         specialize (IHc i  (n + size (bcomp b false (size (ccomp c) + 1))) H s H0).
         split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn. omega.
         unfold IsSucc in H0. destruct H0, H0, H1.
         assert (size [JMP (- (size (bcomp b false (size (ccomp c) + 1)) + size (ccomp c) + 1))] = 1).
         easy. rewrite H3 in H1.
         assert (x = 0) by omega. subst. cbn in *.
         destruct H2. split. subst. omega.
         rewrite !size_app. cbn. subst. 
         rewrite !Z.add_assoc.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size. omega. easy.
Qed.

Lemma ccomp_exits: 
  forall c i, 0 <= i -> forall s,
      IsExit (ccomp c) s ->  s = size (ccomp c).
Proof. intros; unfold IsExit in H0;
       destruct H0; apply (ccomp_succs c i) in H0.
	      Reconstr.hobvious (@H1, @H0)
		      (@Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.add_0_l,
           @Coq.ZArith.BinInt.Z.le_gt_cases)
		      Reconstr.Empty.
       scrush.
Qed.

Lemma lem_znth_app_r :
  forall xs ys i x, i >= 0 -> i < size xs -> znth i (xs ++ ys) x = znth i xs x.
Proof.
  intro xs. induction xs; intros.
  - scrush.
  - rewrite lem_nth_append.
	   Reconstr.hcrush (@H0)
		  (@Compiler.lem_size_succ, @Coq.Bool.Bool.diff_true_false, @Coq.ZArith.Zbool.Zlt_is_lt_bool)
		  (@Compiler.znth, @Coq.ZArith.BinIntDef.Z.succ).
		omega.
Qed.

Lemma exec1_split i j: forall P c P' s s' stk stk',
  exec1 (P ++ c ++ P') (size P + i, s, stk) (j, s', stk') ->
  0 <= i -> i < size c -> exec1 c (i, s, stk) (j - size P, s', stk').
Proof. intros. apply lem_exec1I.
       unfold exec1 in *. destruct H, H, H, H, H2.
       inversion H.
       subst. assert (i >= 0) by omega.
       specialize (lem_znth_app P (c ++ P') i ADD H4); intros.
       rewrite H5 in H2.
       assert (znth i (c ++ P') ADD = znth i c ADD).
       { now rewrite lem_znth_app_r. }
       rewrite H6 in H2.
       specialize (lem_iexec_shift (znth i c ADD) (size P) i 
                                   (j - (size P)) x0 s' x1 stk'); intros.
       assert (size P + (j - size P) = j) by omega.
	     Reconstr.hcrush (@H8, @H2, @H7)
		      Reconstr.Empty
		      Reconstr.Empty.
       scrush. scrush.
Qed.

Axiom classic : forall P:Prop, P \/ ~ P.

Lemma exec_n_split: 
forall (n: nat) P c P' (i j: Z) (s s': state * stack),
  0 <= i -> i < size c ->
  exec_n (P ++ c ++ P') (size P + i, fst s, snd s) n (j, fst s', snd s') ->
  (j < size P \/ j >= size P + size c) ->
  exists s'': state * stack, exists i', exists k, exists m,
    exec_n c (i, fst s, snd s) k (i', fst s'', snd s'') /\ IsExit c i' /\
    exec_n (P ++ c ++ P') (size P + i', fst s'', snd s'') m (j, fst s', snd s') /\
    n%nat = (k + m)%nat.
Proof. intros n. induction n; intros; cbn in *.
       - exists s. exists i. exists O. exists O.
         split. now inversion H1. 
         split. unfold IsExit. split.
         unfold IsSucc. inversion H1. subst.
         destruct H2.
         assert (size P + i < size P -> False) by omega. omega.
         assert (size P + i > size P + size c -> False) by omega. omega.
         inversion H1. subst. destruct H2.
         assert (size P + i < size P -> False) by omega. omega.
         assert (size P + i > size P + size c -> False) by omega. omega.
         split; easy.
       - destruct H1, H1, x, p.
         pose proof H1 as H1a.
         pose proof H3 as H3a.
         apply exec1_split in H1; try easy.
         destruct (classic (0 <= z - size P < size c)).
         destruct H4.
         specialize (IHn P c P' (z - size P) j (s1, s0) s').

         assert (size P + (z - size P) = z) by omega.
         rewrite H6 in IHn. unfold fst, snd in IHn.
         specialize (IHn H4 H5 H3 H2).
         destruct IHn, H7, H7, H7, H7, x, H8, H9, s'.
         exists (s2, s3). exists x0. exists (S x1). exists x2.
         split. cbn.
         exists (z - size P, s1, s0). split. easy.  easy.
         split. easy. split. cbn. easy. omega.

         unfold exec1 in H1. destruct H1, H1, H1, H1, H5.
         apply succs_iexec1 in H5; try omega. cbn in *.
         assert (IsExit c (z - size P)).
         unfold IsExit. split; easy.
         

         exists (s1, s0). exists (z - size P). exists 1%nat. exists n.

         split. cbn. inversion H1.
         apply exec1_split in H1a; try easy.
         exists ((z - size P, s1, s0)). split.
         inversion H1. subst. easy. easy.
         split. easy.
         split.
         assert (size P + (z - size P) = z) by
	       Reconstr.htrivial Reconstr.Empty
		        (@Coq.ZArith.BinInt.Zplus_minus)
		        Reconstr.Empty; scrush.
         scrush.
Qed.


Definition ascii_eqb (a b: Ascii.ascii) :=
  match a, b with
    | Ascii.Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
      Bool.eqb a1 b1 && 
      Bool.eqb a2 b2 &&
      Bool.eqb a3 b3 &&
      Bool.eqb a4 b4 &&
      Bool.eqb a5 b5 &&
      Bool.eqb a6 b6 &&
      Bool.eqb a7 b7 &&
      Bool.eqb a8 b8
  end.

Lemma ascii_eqb_refl: forall a, ascii_eqb a a = true.
Proof. 
       induction a; sauto;
	     Reconstr.hsimple Reconstr.Empty
		      (@Coq.Bool.Bool.eqb_reflx)
		      (@Coq.Init.Datatypes.andb).
Qed.

Fixpoint string_eqb (x y: string) :=
  match x, y with
    | ""%string, ""%string => true
    | String a s1, String b s2 => 
      if ascii_eqb a b then
      string_eqb s1 s2 else false 
     | _, _ => false
   end.
 

Fixpoint instr_eqb (i1 i2: instr): bool :=
  match i1, i2 with
    | JMP i, JMP j         => Z.eqb i j
    | LOAD x, LOAD y       => string_eqb x y
    | LOADI i, LOADI j     => Z.eqb i j
    | ADD, ADD             => true
    | STORE x, STORE y     => string_eqb x y
    | JMPLESS i, JMPLESS j => Z.eqb i j
    | JMPGE i, JMPGE j     => Z.eqb i j
    | _, _                 => false
  end.

Fixpoint list_instr_eqb l m :=
  match l, m with
    | [], [] => true
    | x :: xs, y :: ys => if instr_eqb x y then list_instr_eqb xs ys else false
    | _, _ => false
  end.

Lemma exec_n_drop_right:
  forall (n: nat) (i j: Z) (P c P': list instr) s s',
  exec_n (c ++ P') (0, fst s, snd s) n (j, fst s', snd s') ->
  (j < 0 \/ j >= size c) ->
  exists s'', exists i', exists k, exists m,
  if list_instr_eqb c [] then s'' = s /\ i' = 0 /\ k = O
  else
   exec_n c (0, fst s, snd s) k (i', fst s'', snd s'') /\
   IsExit c i' /\
   exec_n (c ++ P') (i', fst s'', snd s'') m (j, fst s', snd s') /\
   n%nat = (k  + m)%nat.
Proof. intros. case_eq c; intros.
       exists s. exists 0. exists O. exists O. scrush.
       specialize (exec_n_split n [] c P' 0); intros.
       cbn in *. subst.
       specialize (H2 j s s').  cbn in *. 
       assert (0 <= 0) by omega.
       assert (0 < Z.pos (Pos.of_succ_nat (Datatypes.length l))) by scrush.
       specialize (H2 H1 H3 H H0); scrush.
Qed.

Lemma exec1_drop_left:
  forall n i P1 P2 s s' stk stk',
  exec1 (P1 ++ P2) (i, s, stk) (n, s', stk') ->
  size P1 <= i ->
  exec1 P2 (i - size P1, s, stk) (n - size P1, s', stk').
Proof. intros.
       specialize (exec1_split (i - size P1) n P1 P2 []); intros.
       apply H1. assert (P1 ++ P2 ++ [] = P1 ++ P2) by scrush.
	     Reconstr.hobvious (@H, @H2)
		      (@Coq.ZArith.BinInt.Zplus_minus)
		      Reconstr.Empty.
	     Reconstr.htrivial (@H0)
		      (@Coq.ZArith.auxiliary.Zle_left)
		      (@Coq.ZArith.BinIntDef.Z.sub).
       unfold exec1 in H.
       destruct H, H, H, H, H2.
       inversion H.
	     Reconstr.hcrush (@H3)
		      (@Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.opp_involutive, @Coq.ZArith.BinInt.Z.lt_add_lt_sub_r, @Compiler.lem_size_app)
		      (@Coq.ZArith.BinIntDef.Z.sub);
	     Reconstr.hsimple (@H9, @H8, @H4, @H3, @H)
		      Reconstr.Empty
		      (@Coq.ZArith.BinInt.Z.lt).
Qed.


Lemma exec_n_drop_left:
   forall k n i P P' s s' stk stk',
   exec_n (P ++ P') (i, s, stk) k (n, s', stk') ->
   size P <= i -> (forall r, (IsExit P' r) -> r >= 0) ->
   exec_n P' (i - size P, s, stk) k (n - size P, s', stk').
Proof. intro k. induction k; intros.
        - scrush.
        - cbn in *. destruct H, H, x, p.
          eapply exec1_drop_left in H.
          exists ((z - size P, s1, s0)). split. scrush.
          apply IHk. easy.
          unfold exec1 in H.
          destruct H, H, H, H, H3.
          apply succs_iexec1 in H3. cbn in *.

          inversion H3. destruct H5, H6.
          cbn in *.

          specialize (H1 (z - size P)).
          unfold IsExit in H1.
	        Reconstr.hexhaustive 1 (@H3, @H1)
		        (@Coq.ZArith.BinInt.Z.le_0_sub, @Coq.ZArith.BinInt.Z.ge_le_iff)
		        (@Coq.ZArith.BinInt.Z.ge);
	        Reconstr.heasy (@H1, @H0, @H4)
		        Reconstr.Empty
		        (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinIntDef.Z.sub).
          omega. omega. scrush. scrush.
Qed.

Definition closed P := forall r, IsExit P r -> r = size P.

Lemma ccomp_closed: forall c, closed (ccomp c).
Proof.
 unfold closed;
	Reconstr.hobvious Reconstr.Empty
		(@ccomp_exits)
		(@IsExit, @IsSucc).
Qed.

Lemma acomp_closed: forall c, closed (acomp c).
Proof. 
 unfold closed;
	Reconstr.htrivial Reconstr.Empty
		(@acomp_exits)
		Reconstr.Empty.
Qed.

Lemma exec_n_split_full:
   forall k P P' j s s' stk stk',
   exec_n (P ++ P') (0,s,stk) k (j, s', stk') ->
   size P <= j ->
   closed P ->
   (forall r, (IsExit P' r) -> r >= 0) ->
   exists k1, exists k2, exists s'', exists stk'',
     exec_n P (0,s,stk) k1 (size P, s'', stk'') /\
     exec_n P' (0,s'',stk'') k2 (j - size P, s', stk').
Proof. intros.
        case_eq P; intros; subst.
        cbn in *. exists O. exists k. exists s. exists stk. scrush.

        specialize (exec_n_split k [] (i :: l) P' 0 j (s, stk) (s', stk')); intros.

        assert (0 <= 0) by omega.
        assert (0 < Z.pos (Pos.of_succ_nat (Datatypes.length l))) by scrush.
        specialize (H3 H4 H5).
        pose proof H2 as H2a.
        specialize (H2 (j - size (i :: l))).
        assert (j < 0 \/ j >= Z.pos (Pos.of_succ_nat (Datatypes.length l))).
        right. cbn in H0. omega.
        cbn in H3.
        specialize (H3 H H6).
        unfold closed in *.
        destruct H3, H3, H3, H3, H3, H7, H8.
        specialize (H1 x0 H7).
        rewrite H1 in *.
        destruct x. unfold fst, snd in H8.
        assert (i :: l ++ P' = (i :: l) ++ P'). easy.
        rewrite H10 in H8.
        eapply exec_n_drop_left in H8.

        exists x1. exists x2. exists s0. exists s1.
        split. easy.
        assert (size (i :: l) - size (i :: l) = 0) by omega.
        rewrite H11 in *. easy.
        omega. easy.
Qed.

Lemma acomp_neq_Nil: forall a, acomp a <> [].
Proof. induction a; sauto.
       assert (forall l, l ++ [ADD] <> []). scrush.
       assert (forall l m, l ++ m ++ [ADD] <> []). scrush.
       scrush.
Qed.

Lemma helper_acomp_exec_n: forall a1 a2 (n: nat) (s s': state) (stk stk': stack),
(forall (n : nat) (s s' : state) (stk stk' : stack),
    exec_n (acomp a2) (0, s, stk) n (size (acomp a2), s', stk') -> stk' = aval s a2 :: stk) ->
(forall (n : nat) (s s' : state) (stk stk' : stack),
     exec_n (acomp a2) (0, s, stk) n (size (acomp a2), s', stk') -> s' = s) ->
(forall (n : nat) (s s' : state) (stk stk' : stack),
     exec_n (acomp a1) (0, s, stk) n (size (acomp a1), s', stk') -> stk' = aval s a1 :: stk) ->
(forall (n : nat) (s s' : state) (stk stk' : stack),
     exec_n (acomp a1) (0, s, stk) n (size (acomp a1), s', stk') -> s' = s) ->
 exec_n (acomp a1 ++ acomp a2 ++ [ADD]) (0, s, stk) n (size (acomp a1 ++ acomp a2 ++ [ADD]), s', stk') ->
s' = s /\ stk' = aval s a1 + aval s a2 :: stk.
Proof.  intros.
        apply exec_n_split_full in H3.
        destruct H3, H3, H3, H3, H3.
        apply exec_n_split_full in H4.
        destruct H4, H4, H4, H4, H4. 
        rewrite !size_app, Z.add_comm in H5.
        assert (size (acomp a2) + size [ADD] + size (acomp a1) 
        - size (acomp a1) - size (acomp a2) = size [ADD]).
        Reconstr.htrivial Reconstr.Empty
	        (@Coq.ZArith.BinInt.Z.add_simpl_r, @Coq.ZArith.BinInt.Z.add_simpl_l)
	        (@Coq.ZArith.BinIntDef.Z.sub, @Compiler.size).
        rewrite H6 in H5.
        assert (size [ADD] = 1) by scrush.
        rewrite H7 in *.
        apply exec_n_step in H5; try easy.
        destruct H5, H5, H8, x7, p.
        eapply exec_n_end in H8; scrush.
        rewrite !size_app, Z.add_comm.
        assert (size (acomp a2) + size [ADD] + size (acomp a1) - size (acomp a1) =
                size (acomp a2) + size [ADD]) by omega.
        rewrite H5.
        assert (size [ADD] = 1) by scrush. omega.
        unfold closed. intros.
        unfold IsExit, IsSucc in H5.
        destruct H5, H5, H5, H7.
        Reconstr.hobvious (@H6, @H7, @H5, @H8)
	        (@acomp_exits)
	        (@IsSucc, @IsExit).
        intros; sauto;
        Reconstr.hsimple (@H5)
          (@Coq.ZArith.Zcompare.Zcompare_Gt_not_Lt, @Coq.ZArith.Zcompare.Zcompare_Gt_Lt_antisym)
          (@Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.le).
        rewrite !size_app, Z.add_comm.
        assert (size [ADD] = 1) by scrush.
        assert (size (acomp a2) >= 0) by apply list_size.
        omega.
        unfold closed. intros.
        unfold IsExit, IsSucc in H4.
        destruct H4, H4, H4, H6.
        Reconstr.hobvious (@H5, @H6, @H4, @H7)
	        (@acomp_exits)
	        (@IsSucc, @IsExit).

	      intros.
	      unfold IsExit in *.
	      assert (0 > r \/ r >= size (acomp a2 ++ [ADD])). omega.
	      destruct H4, H5.
	      apply succs_append in H4. cbn in *.
	      destruct H4. apply acomp_succs in H4.
	       omega.
	      unfold IsSucc in H4.
	      destruct H4, H4, H7.
	      assert (x = 0) by (cbn in *; omega).
	      rewrite H9 in *. cbn in *.
	      destruct H8.
	      rewrite  <- H8 in H5.
	      assert (size (acomp a2) >= 0) by apply list_size.
	      omega. easy. rewrite size_app in H5.
	      assert (size (acomp a2) >= 0) by apply list_size.
	      assert (size [ADD] = 1) by scrush.
	      omega.
Qed.

Lemma acomp_exec_n:
  forall a n s s' stk stk',
  exec_n (acomp a) (0,s,stk) n (size (acomp a),s',stk') ->
  s' = s /\ stk' = (aval s a) :: stk.
Proof.  induction a; sauto;
        try
         (apply exec_n_step in H; try easy;
         destruct H, H, H0, x, p;
         eapply exec_n_end in H0; scrush;
         scrush);
         apply (helper_acomp_exec_n a1 a2 n s s' stk stk'); easy.
Qed.

Lemma bcomp_split:
  forall n i j b f P' s s' stk stk',
  exec_n (bcomp b f i ++ P') (0, s, stk) n (j, s', stk') ->
  (j < 0 \/ j >= size (bcomp b f i)) -> 
  0 <= i ->
  exists s'', exists stk'', exists i', exists k, exists m,
    exec_n (bcomp b f i) (0, s, stk) k (i', s'', stk'') /\
    (i' = size (bcomp b f i) \/ i' = i + size (bcomp b f i)) /\
    exec_n (bcomp b f i ++ P') (i', s'', stk'') m (j, s', stk') /\
    n%nat = (k + m)%nat.
Proof. intros; case_eq (bcomp b f i); intros; rewrite H2 in *;
       try (exists s; exists stk; exists 0; exists O; exists n; scrush);

       pose proof H as Ha;
       specialize (exec_n_drop_right n i j [] (i0 :: l) P' (s, stk) (s', stk')); intros;
       unfold fst, snd in H3; specialize (H3 H H0);
       destruct H3, H3, H3, H3, x; cbn in H3;
       exists s0; exists s1; exists x0; exists x1; exists x2;

       split; try easy; split; destruct H3, H4;
       rewrite <- H2 in *;
       unfold IsExit in H4; destruct H4;
       apply bcomp_succs in H4; try easy;
       destruct H4; try(
	     Reconstr.hobvious (@H6, @H4)
		      (@Coq.ZArith.Zorder.Zle_lt_or_eq, @Coq.ZArith.BinInt.Z.add_0_l)
		      Reconstr.Empty; scrush); scrush.
Qed.

Lemma neq_eqb: forall b1 b2, eqb b1 (negb b2) = eqb (negb b1) b2.
Proof. scrush. Qed.

Lemma bcomp_exec_n:
  forall b n i j f s s' stk stk',
  exec_n (bcomp b f j) (0, s, stk) n (i, s', stk') ->
  size (bcomp b f j) <= i -> 0 <= j ->
  i = size(bcomp b f j) + (if Bool.eqb (bval s b) f then j else 0) /\
  s' = s /\ stk' = stk.
Proof. intro b; induction b; intros.
       - cbn in *.
         case_eq (eqb b f); intros; rewrite H2 in *.
         pose proof H as Ha.
         apply exec_n_step in H; try easy.
         destruct H, H, H3, x, p.
         eapply exec_n_end in H3; scrush.
         cbn in *. omega.
         eapply exec_n_end in H; scrush.
       - specialize (IHb n i j (negb f) s s' stk stk' H H0 H1);
         split. case_eq (eqb (bval s b) (negb f) ); intros.
         rewrite H2 in *. cbn.
         assert (eqb (negb (bval s b)) f = true) by (pose neq_eqb; scrush).
         rewrite H3 in *. easy.
         rewrite H2 in *. cbn.
         assert (eqb (negb (bval s b)) f = false) by (pose neq_eqb; scrush).
         rewrite H3 in *. easy. easy.
       - case_eq f; intros.
         rewrite H2 in *.
         case_eq ((bval s (Band b1 b2))); intros. cbn.
         + cbn in H3.
           assert (bval s b1 = true) by scrush.
           assert (bval s b2 = true) by scrush.
           cbn in H.
           apply bcomp_split in H.
           destruct H, H, H, H, H, H, H6, H7.
           eapply exec_n_drop_left in H7.
           destruct H6; rewrite H6 in *.
           assert (size (bcomp b1 false (size (bcomp b2 true j))) - 
                   size (bcomp b1 false (size (bcomp b2 true j))) = 0). omega.
           rewrite H9 in *.
           specialize (IHb2 x3
                            (i - size (bcomp b1 false (size (bcomp b2 true j)))) 
                            j true x s' x0 stk' H7).
           cbn in H0. rewrite size_app in H0.
           assert (size (bcomp b2 true j) <= 
                   i - size (bcomp b1 false (size (bcomp b2 true j)))) by omega.
           specialize (IHb2 H10 H1).
           destruct IHb2.
           specialize (IHb1 x2 
                            (size (bcomp b1 false (size (bcomp b2 true j))))
                            (size (bcomp b2 true j)) false s s' stk stk').
           destruct H12. rewrite H12, H13 in *.
           specialize (IHb1 H).
           assert (size (bcomp b1 false (size (bcomp b2 true j))) <= 
                   size (bcomp b1 false (size (bcomp b2 true j)))) by omega.
           assert (size (bcomp b2 true j) >= 0) by eapply list_size.
           assert (0 <= size (bcomp b2 true j)) by omega.
           specialize (IHb1 H14 H16).
           destruct IHb1, H18. subst. rewrite H5 in H11.
           cbn in H11. rewrite size_app. split. omega. easy.
         
           assert (size (bcomp b2 true j) + 
                   size (bcomp b1 false (size (bcomp b2 true j))) -
                   size (bcomp b1 false (size (bcomp b2 true j))) = 
                   size (bcomp b2 true j)) by omega.
           rewrite H9 in *.
         
           specialize (IHb1 x2
           (size (bcomp b2 true j) + size (bcomp b1 false (size (bcomp b2 true j))))
           (size (bcomp b2 true j)) false s x stk x0 H).
           assert (size (bcomp b1 false (size (bcomp b2 true j))) <=
                   size (bcomp b2 true j) + size (bcomp b1 false (size (bcomp b2 true j)))).
           assert (size (bcomp b2 true j) >= 0) by apply list_size.
           assert (size (bcomp b1 false (size (bcomp b2 true j))) >= 0) by apply list_size.
           omega.
           assert (0 <= size (bcomp b2 true j)).
           assert (size (bcomp b2 true j) >= 0) by apply list_size. omega.
           specialize (IHb1 H10 H11).
           destruct IHb1. destruct H13.
           rewrite H13, H14 in *.
           rewrite H4 in H12. cbn in H12.
           assert (size (bcomp b2 true j) = 0) by omega.
           rewrite H15 in *.
           specialize (IHb2 x3 (i - size (bcomp b1 false 0)) j true s s' stk stk' H7).
           cbn in *. rewrite size_app in H0.
           rewrite H15 in *.
           assert (0 <= i - size (bcomp b1 false 0)) by omega.
           specialize (IHb2 H16 H1).
           destruct IHb2. rewrite H5 in H17. cbn in *.
           rewrite size_app, H15. split. omega. easy.
         
           destruct H6. scrush.
           assert (size (bcomp b2 true j) >= 0) by apply list_size.
           omega.
           
           intros. unfold IsExit in *.
           destruct H9.
           assert (0 > r \/ r >= size (bcomp b2 true j)) by omega.
           apply bcomp_succs in H9; try easy.
           destruct H9.
           destruct H11. omega. omega.
           assert (size (bcomp b2 true j) >= 0) by apply list_size.
           omega.

           right. cbn in *. rewrite size_app in H0.
           assert (size (bcomp b2 true j) >= 0) by apply list_size.
           omega.
           assert (size (bcomp b2 true j) >= 0) by apply list_size.
           omega.
         + cbn in *.
Admitted.


Lemma app_nil: forall {A} (l m: list A), l ++ m = [] -> l = [] /\ m = [].
Proof. scrush. Qed.

Lemma ccomp_empty:
  forall c s, ccomp c = [] -> Big_Step.big_step (c, s) s.
Proof. intro c; induction c; intros; cbn; try (pose @app_nil; scrush);
        cbn in *; apply app_nil in H;
	       Reconstr.hobvious (@IHc2, @H, @IHc1)
		       (@Big_Step.SeqSem)
		       Reconstr.Empty.
Qed.


