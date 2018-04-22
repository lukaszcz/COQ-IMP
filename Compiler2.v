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
       unfold In in *.
       destruct H1. left. omega.
       destruct H1. right. left. omega.
       scrush.
       unfold In in *.
       destruct H1. left. omega.
       destruct H1. right. left. omega.
       scrush.
       unfold IsSucc, isuccs in H. destruct H.
       exists x. split. easy. split. easy.
       destruct H, H0; cbn in *;
       case_eq (znth x P ADD); intros; rewrite H2 in *; try now apply In_help.
       unfold In in H1. destruct H1.
       simpl. left. omega.
       scrush.
       unfold In in H1. destruct H1.
       simpl. left. omega.
       unfold In in H1. destruct H1.
       simpl. right. left. omega.
       scrush.
       unfold In in H1. destruct H1.
       simpl. left. omega.
       destruct H1.
       simpl. right. left. omega.
       scrush.
Qed.

Lemma helper: forall y n, n + 1 + Z.of_nat y = n + Z.of_nat (1 + y).
Proof. intro n; induction n; intros.
       - cbn. scrush.
       - specialize (Z.add_cancel_l (1 + Z.of_nat (S n)) (Z.of_nat (1 + S n)) n0); intros.
         rewrite <- Z.add_assoc.
         apply H. scrush.
Qed.

Lemma succs_append_l: forall xs ys n s, IsSucc (xs ++ ys) n s -> IsSucc xs n s \/ IsSucc ys (n + size xs) s.
Proof. intro xs; induction xs; intros.
       - cbn in *. assert (n + 0 = n) by scrush. rewrite H0. now right.
       - intros. cbn in H. apply succs_Cons in H.
         destruct H.
         left. apply succs_Cons. now left.
         specialize (IHxs ys (n + 1) s H).
         destruct IHxs. left.
         apply succs_Cons. now right.
         right. unfold size in *.
         assert (Datatypes.length (a :: xs) = (1 + Datatypes.length xs)%nat) by scrush.
         rewrite H1. pose helper; scrush.
Qed.

Lemma succs_append_r: forall xs ys n s, IsSucc xs n s \/ IsSucc ys (n + size xs) s -> IsSucc (xs ++ ys) n s.
Proof. intro xs; induction xs; intros.
       - cbn in *. assert (n + 0 = n) by scrush. rewrite H0 in *.
         destruct H.
         unfold IsSucc in *. destruct H.
         destruct H, H1. cbn in *. contradict H. omega.
         easy.
       - destruct H. apply succs_Cons in H.
         cbn. apply succs_Cons. destruct H.
         now left. right. apply IHxs. now left.
         cbn. apply succs_Cons. right. apply IHxs.
         right. unfold size in *.
         assert (Datatypes.length (a :: xs) = (1 + Datatypes.length xs)%nat) by scrush.
         rewrite H0 in H. pose helper; scrush.
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
    rewrite HH; clear HH.
    pose succs_shift; scrush.
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
Proof. unfold IsExit, IsSucc. intros.
       split. exists 0. split. easy.
       split. easy. cbn in *.
       scrush. cbn.
       omega.
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
Proof. split; intros. unfold IsExit in H.
       destruct H. cbn in *. destruct H, H, H1. cbn in *.
       contradict H. omega.
       unfold IsExit. split. unfold IsSucc.
       exists 0. split. easy. split. easy. cbn. left.
       unfold In in *. easy.
       cbn in *. easy.
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
Proof. unfold IsExit; intros;
       destruct H0; apply bcomp_succs in H0; destruct H0; cbn in *.
       - left; destruct H0; omega.
       - right; omega.
       - omega.
Qed.

Lemma bcomp_existsD: 
  forall b f i, 0 <= i -> forall s, exists s',
      IsExit (bcomp b f i) s ->
      s' = size (bcomp b f i) \/ s' <= i + size (bcomp b f i).
Proof. intros; exists s; apply bcomp_exits; easy. Qed.

Lemma size_app: forall l m, size (l ++ m) = size l + size m.
Proof. unfold size; intros.
       rewrite app_length.
       Reconstr.htrivial Reconstr.Empty
		    (@Coq.ZArith.Znat.Nat2Z.inj_add)
		    Reconstr.Empty.
Qed.

Lemma ccomp_size: forall c, size (ccomp c) >= 0.
Proof. intro c; case_eq (ccomp c); intros;
       unfold size; simpl; easy.
Qed.

Lemma list_size: forall l, size l >= 0.
Proof. intro l; case_eq l; intros;
       unfold size; simpl; easy.
Qed.

Lemma ccomp_succs: 
  forall c i n, 0 <= i -> forall s,
      IsSucc (ccomp c) n s -> n <= s <= n + size (ccomp c).
Proof. intro c; induction c; intros.
       - cbn in *; pose (succs_empty n s); easy.
       - cbn in *. specialize (succs_append (acomp a) [STORE v] n s); intros.
         apply H1 in H0. destruct H0.
         apply acomp_succs in H0.
         assert (size (acomp a ++ [STORE v]) = size (acomp a) + 1).
         unfold size. cbn. rewrite app_length. cbn.
         rewrite Nat2Z.inj_add. easy.
         rewrite H2. omega.
         unfold IsSucc in *. destruct H0, H0, H2.
         assert (x = 0). unfold size in H2. cbn in H2. 
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
         case_eq (ccomp c2); intros; subst.
         assert (ccomp c1 ++ [] = ccomp c1) by scrush.
         rewrite H3. easy.
         cbn in *. unfold size. rewrite app_length. cbn.
         unfold size in IHc1.
         split. omega.
         assert (Z.of_nat (Datatypes.length (ccomp c1) + S (Datatypes.length l)) = 
         Z.of_nat (Datatypes.length (ccomp c1) + (Datatypes.length l) + 1)).
         f_equal. omega.
         rewrite H3.
         rewrite !Nat2Z.inj_add. omega.
         specialize (IHc2 i (n + size (ccomp c1)) H s H0).
         rewrite size_app. split. pose acomp_size.
         destruct IHc2. 
         specialize (ccomp_size c1); intros.
         omega. omega.
       - cbn in *.
         apply succs_append in H0.
         destruct H0.
         apply bcomp_succs in H0.
         destruct H0.
         rewrite !size_app. cbn.
         split. omega.
         destruct H0.
         specialize (ccomp_size c1); intros.
         specialize (ccomp_size c2); intros.
         rewrite !Z.add_assoc.
         assert ( Z.pos (Pos.of_succ_nat (Datatypes.length (ccomp c2))) >= 0) by scrush.
         omega.
         subst. cbn.
         split.
         rewrite Z.add_assoc.
         specialize (ccomp_size c1); intros.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0).
         apply list_size. omega.
         rewrite !size_app. unfold size.
         cbn. rewrite !Z.add_assoc. 
         rewrite Zpos_P_of_succ_nat. omega.
         remember (ccomp_size c1); intros.
         omega.
         apply succs_append in H0.
         destruct H0.
         specialize (IHc1 i (n + size (bcomp b false (size (ccomp c1) + 1))) H s H0).
         split. destruct IHc1.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0).
         apply list_size. omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat. omega.
         apply succs_Cons in H0.
         destruct H0. cbn in *.
         destruct H0. subst.
         split.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c1) >= 0) by apply list_size.
         assert (size (ccomp c2) >= 0) by apply list_size.
         omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat.
         unfold size in *. omega.
         easy.
         specialize (IHc2 i (n + size (bcomp b false (size (ccomp c1) + 1)) + size (ccomp c1) + 1) H s H0).
         destruct IHc2. split.
         assert (size (bcomp b false (size (ccomp c1) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c1) >= 0) by apply list_size.
         assert (size (ccomp c2) >= 0) by apply list_size.
         omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         rewrite Zpos_P_of_succ_nat.
         unfold size in *. omega.
       - cbn in *.
         apply succs_append in H0.
         destruct H0.
         apply bcomp_succs in H0.
         destruct H0.
         assert (Datatypes.length [JMP (- (size (bcomp b false (size (ccomp c) + 1)) + size (ccomp c) + 1))] = 1%nat).
         easy.
         split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         omega.
         rewrite !size_app, !Z.add_assoc. cbn.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size.
         omega.
         subst.
         split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size.
         omega.
         rewrite !size_app, !Z.add_assoc. cbn. omega.
         unfold size. omega.
         apply succs_append in H0.
         destruct H0.
         specialize (IHc i  (n + size (bcomp b false (size (ccomp c) + 1))) H s H0).
         split.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         omega.
         rewrite !size_app, !Z.add_assoc. cbn. omega.
         unfold IsSucc in H0. destruct H0, H0, H1.
         assert (size [JMP (- (size (bcomp b false (size (ccomp c) + 1)) + size (ccomp c) + 1))] = 1).
         easy. rewrite H3 in H1.
         assert (x = 0) by omega. subst.
         cbn in *.
         destruct H2.
         split. subst. omega.
         rewrite !size_app. cbn. subst. 
         rewrite !Z.add_assoc.
         assert (size (bcomp b false (size (ccomp c) + 1)) >= 0) by apply list_size.
         assert (size (ccomp c) >= 0) by apply list_size.
         omega.
         easy.
Qed.

Lemma ccomp_exits: 
  forall c i, 0 <= i -> forall s,
      IsExit (ccomp c) s ->  s = size (ccomp c).
Proof. intros. unfold IsExit in H0. 
       destruct H0. apply (ccomp_succs c i) in H0.
       cbn in *. 
       unfold Logic.not in H1.
       omega. omega.
Qed.


