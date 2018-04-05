Require Import Com.
Require Import Big_Step.
Require Import Star.
Local Open Scope Z_scope.

Inductive instr :=
| LOADI : Z -> instr
| LOAD : vname -> instr
| ADD : instr
| STORE : vname -> instr
| JMP : Z -> instr
| JMPLESS : Z -> instr
| JMPGE : Z -> instr.

Definition stack := list val.
Definition config : Set := Z * state * stack.

Definition iexec (ins : instr) (cfg : config) : config :=
  match cfg with
  | (i, s, stk) =>
    match ins with
    | LOADI n => (i + 1, s, n :: stk)
    | LOAD x => (i + 1, s, s x :: stk)
    | ADD => (i + 1, s, hd 0 (tl stk) + hd 0 stk :: tl (tl stk))
    | STORE x => (i + 1, update s x (hd 0 stk), tl stk)
    | JMP n => (i + 1 + n, s, stk)
    | JMPLESS n => (if (hd 0 (tl stk)) <? hd 0 stk then i + 1 + n else i + 1, s, tl (tl stk))
    | JMPGE n => (if (hd 0 (tl stk)) >=? hd 0 stk then i + 1 + n else i + 1, s, tl (tl stk))
    end
  end.

Definition size (P : list instr) := Z.of_nat (length P).
Definition znth {A} (n : Z) (l : list A) (x : A) := nth (Z.to_nat n) l x.

Definition exec1 (P : list instr) (c c' : config) : Prop :=
  exists i s stk, c = (i,s,stk) /\ c' = iexec (znth i P ADD) (i,s,stk)
                  /\ i >= 0 /\ i < size P.

Definition exec P := star (exec1 P).
Hint Unfold exec : yhints.

Lemma lem_exec1I :
  forall P i s stk c', c' = iexec (znth i P ADD) (i,s,stk) ->
                       0 <= i -> i < size P ->
                       exec1 P (i,s,stk) c'.
Proof.
  Reconstr.hobvious Reconstr.Empty
                    (@Coq.ZArith.BinInt.Z.lt_nge)
                    (@Coq.ZArith.BinInt.Z.ge, @znth, @exec1, @Coq.ZArith.BinInt.Z.lt).
Qed.

(* Helper instruction list functions *)

Lemma lem_n_succ_znth :
  forall {A} n (a : A) xs x, 0 <= n -> znth (n + 1) (a :: xs) x = znth n xs x.
Proof.
  induction n; sauto.
  - Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.Pnat.Pos2Nat.inj_succ, @Coq.PArith.BinPos.Pos.add_1_r)
                      Reconstr.Empty.
  - Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.BinPos.Pos.add_1_r, @Coq.PArith.Pnat.Pos2Nat.inj_succ,
                       @Coq.ZArith.Znat.Z2Nat.inj_pos, @Coq.Init.Peano.eq_add_S)
                      (@znth).
Qed.

Lemma lem_znth_app :
  forall xs ys i x, i >= 0 -> znth (size xs + i) (xs ++ ys) x = znth i ys x.
Proof.
  assert (forall n (xs ys : list instr) i x, i >= 0 -> n = length xs ->
                                             znth (Z.of_nat n + i) (xs ++ ys) x = znth i ys x);
    [idtac | scrush].
  induction n.
  - scrush.
  - assert (HH: Z.of_nat (S n) = Z.of_nat n + 1) by
        Reconstr.htrivial Reconstr.Empty
                          (@Coq.ZArith.Znat.Nat2Z.inj_succ)
                          (@Coq.ZArith.BinIntDef.Z.succ).
    rewrite HH; clear HH.
    intros xs ys i x H1 H2.
    assert (0 <= Z.of_nat n + i) by omega.
    assert (HH: Z.of_nat n + 1 + i = (Z.of_nat n + i) + 1) by omega.
    rewrite HH; clear HH.
    destruct xs; [ scrush | simpl ].
    rewrite lem_n_succ_znth by scrush.
    scrush.
Qed.

Lemma lem_size_succ :
  forall a xs, size (a :: xs) = size xs + 1.
Proof.
  assert (forall n a xs, n = size xs -> size (a :: xs) = n + 1); [idtac | scrush].
  induction n; sauto.
  - scrush.
  - Reconstr.htrivial Reconstr.AllHyps
                      (@Coq.PArith.BinPos.Pplus_one_succ_r, @Coq.ZArith.Znat.Zpos_P_of_succ_nat,
                       @Coq.ZArith.BinInt.Pos2Z.inj_succ)
                      (@Coq.ZArith.BinIntDef.Z.succ, @size).
  - scrush.
Qed.

Lemma lem_nth_append :
  forall xs ys i x, 0 <= i ->
                    znth i (xs ++ ys) x =
                    (if i <? size xs then znth i xs x else znth (i - size xs) ys x).
Proof.
  induction xs.
  - sauto.
    + Reconstr.hcrush Reconstr.AllHyps
                  (@Coq.ZArith.BinInt.Z.ltb_ge)
                  Reconstr.Empty.
    + scrush.
    + scrush.
  - intros.
    assert (HH: i = 0 \/ exists i', i = i' + 1 /\ 0 <= i') by
        Reconstr.hcrush Reconstr.AllHyps
                        (@Coq.ZArith.BinInt.Z.lt_le_pred, @Coq.ZArith.BinInt.Z.lt_eq_cases,
                         @Coq.ZArith.BinInt.Z.succ_pred)
                        (@Coq.ZArith.BinIntDef.Z.succ).
    destruct HH as [ ? | HH ].
    scrush.
    destruct HH as [ i' HH ].
    destruct HH.
    subst; simpl.
    repeat rewrite lem_n_succ_znth by scrush.
    repeat rewrite lem_size_succ.
    sauto.
    + assert ((i' <? size xs) = true).
      Reconstr.hcrush Reconstr.AllHyps
                      (@Coq.ZArith.BinInt.Z.le_gt_cases, @Coq.Bool.Bool.diff_true_false,
                       @Coq.ZArith.BinInt.Z.ltb_ge, @Coq.ZArith.Zbool.Zlt_is_lt_bool,
                       @Coq.ZArith.BinInt.Z.add_le_mono_r)
                      (@size).
      scrush.
    + assert ((i' <? size xs) = false).
      Reconstr.heasy Reconstr.AllHyps
                     (@Coq.ZArith.BinInt.Z.ltb_nlt, @Coq.ZArith.BinInt.Z.add_lt_mono_r)
                     (@size).
      assert (i' + 1 - (size xs + 1) = i' - size xs) by auto with zarith.
      scrush.
Qed.

Lemma lem_size_app : forall xs ys, size (xs ++ ys) = size xs + size ys.
Proof.
  Reconstr.htrivial Reconstr.Empty
                    (@Coq.ZArith.Znat.Nat2Z.inj_add, @Coq.Lists.List.app_length)
                    (@size).
Qed.

Lemma lem_size_app_le : forall xs ys, size xs <= size (xs ++ ys).
Proof.
  Reconstr.hobvious Reconstr.Empty
                    (@Coq.Arith.Plus.le_plus_l, @Coq.ZArith.Znat.Nat2Z.inj_le, @Coq.Lists.List.app_length)
                    (@size).
Qed.

(* Verification infrastructure *)

Lemma lem_iexec_shift :
  forall x n i i' s s' stk stk',
    (n+i',s',stk') = iexec x (n+i,s,stk) <->
    (i',s',stk') = iexec x (i,s,stk).
Proof.
  split; intro H.
  - assert (forall n i i' k, n + i' = n + i + k -> i' = i + k) by auto with zarith.
    assert (forall n i i' k, n + i' = n + i + 1 + k -> i' = i + 1 + k) by auto with zarith.
    scrush.
  - assert (forall n i i' k, i' = i + k -> n + i' = n + i + k) by auto with zarith.
    assert (forall n i, n + (i + 1) = n + i + 1) by auto with zarith.
    scrush. (* takes 25s *)
Qed.

Lemma lem_exec1_hlp1 :
  forall n P P', 0 <= n -> n < size P ->
                 znth n P ADD = znth n (P ++ P') ADD.
Proof.
  induction n.
  - scrush.
  - Reconstr.hcrush Reconstr.Empty
                    (@lem_size_succ, @lem_nth_append, @Coq.ZArith.Zbool.Zlt_is_lt_bool)
                    Reconstr.Empty.
  - scrush.
Qed.

Lemma lem_exec1_appendR :
  forall P P' c c', exec1 P c c' -> exec1 (P ++ P') c c'.
Proof.
  unfold exec1.
  intros; simp_hyps.
  exists i.
  exists s.
  exists stk.
  rewrite <- lem_exec1_hlp1 by auto with zarith.
  assert (i < size (P ++ P')) by
      Reconstr.heasy Reconstr.AllHyps
                     (@lem_size_app_le, @Coq.ZArith.BinInt.Z.le_lt_trans,
                      @Coq.ZArith.BinInt.Z.nle_gt, @Coq.ZArith.BinInt.Z.lt_ge_cases)
                     (@size).
  scrush.
Qed.

Lemma lem_exec_appendR : forall P P' c c', exec P c c' -> exec (P ++ P') c c'.
Proof.
  unfold exec.
  intros P P' c c' H.
  induction H.
  - scrush.
  - pose @star_step; pose lem_exec1_appendR; scrush.
Qed.

Lemma lem_exec1_appendL :
  forall i i' P P' s s' stk stk', exec1 P (i,s,stk) (i',s',stk') ->
                                  exec1 (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk').
Proof.
  unfold exec1.
  intros; simp_hyps.
  exists (size P' + i0).
  exists s0.
  exists stk0.
  rewrite lem_znth_app by scrush.
  split; [ scrush | split ].
  - Reconstr.htrivial Reconstr.AllHyps
                      (@lem_iexec_shift)
                      Reconstr.Empty.
  - split.
    + Reconstr.hobvious Reconstr.AllHyps
                        (@Coq.ZArith.Zorder.Zle_0_nat, @Coq.ZArith.BinInt.Z.nle_gt,
                         @Coq.ZArith.BinInt.Z.add_neg_cases)
                        (@size, @Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.lt).
    + Reconstr.hobvious Reconstr.AllHyps
                        (@lem_size_app, @Coq.ZArith.BinInt.Z.add_lt_mono_l)
                        (@size).
Qed.

Lemma lem_exec_appendL :
  forall i i' P P' s s' stk stk', exec P (i,s,stk) (i',s',stk') ->
                                  exec (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk').
Proof.
  assert (forall c c' P, exec P c c' ->
                       forall i i' P' s s' stk stk',
                         c = (i,s,stk) -> c' = (i',s',stk') ->
                         exec (P' ++ P) (size P' + i,s,stk) (size P' + i',s',stk')); [idtac|scrush].
  unfold exec.
  intros c c' P H.
  induction H.
  - scrush.
  - intros; simp_hyps; subst.
    destruct y as [ p stk0 ].
    destruct p as [ i0 s0 ].
    pose @star_step; pose lem_exec1_appendL; scrush.
Qed.

Lemma lem_exec_Cons_1 :
  forall ins P j s t stk stk',
    exec P (0,s,stk) (j,t,stk') ->
    exec (ins :: P) (1,s,stk) (1+j,t,stk').
Proof.
  intros ins P j.
  assert (HH: ins :: P = (ins :: nil) ++ P) by auto with datatypes.
  rewrite HH; clear HH.
  assert (HH: 1 + j = size (ins :: nil) + j) by scrush.
  rewrite HH; clear HH.
  assert (HH: 1 = size (ins :: nil) + 0) by scrush.
  rewrite HH; clear HH.
  pose lem_exec_appendL; scrush.
Qed.

Lemma lem_exec_appendL_if :
  forall i i' j P P' s s' stk stk',
    size P' <= i -> exec P (i - size P',s,stk) (j,s',stk') -> i' = size P' + j ->
    exec (P' ++ P) (i,s,stk) (i',s',stk').
Proof.
  intros.
  pose (k := i - size P').
  assert (HH: i = size P' + k) by
      Reconstr.htrivial Reconstr.Empty
                        (@Coq.ZArith.BinInt.Zplus_minus)
                        (@k).
  rewrite HH; clear HH.
  pose lem_exec_appendL; scrush.
Qed.

Lemma lem_exec_append_trans :
  forall i' i'' j'' P P' s s' s'' stk stk' stk'',
    exec P (0,s,stk) (i',s',stk') -> size P <= i' ->
    exec P' (i' - size P,s',stk') (i'',s'',stk'') ->
    j'' = size P + i'' ->
    exec (P ++ P') (0,s,stk) (j'',s'',stk'').
Proof.
  intros.
  assert (exec (P ++ P') (i',s',stk') (j'',s'',stk'')) by
      (apply lem_exec_appendL_if with (j := i''); sauto).
  assert (exec (P ++ P') (0,s,stk) (i',s',stk')) by
      (apply lem_exec_appendR; sauto).
  pose @lem_star_trans; scrush.
Qed.

Ltac escrush := unfold exec; pose @star_step; pose @star_refl; scrush.

Ltac exec_tac :=
  match goal with
  | [ |- exec ?A (?i, ?s, ?stk) ?B ] =>
    assert (exec1 A (i, s, stk) B) by
        (unfold exec1; exists i; exists s; exists stk; sauto);
    escrush
  end.

Ltac exec_append_tac :=
  intros; assert (H_exec_append_tac: forall l, size l - size l = 0) by (intro; omega);
  match goal with
  | [ |- exec (?l1 ++ ?l2) (0,?s,?stk) (size(?l1 ++ ?l2), ?s, ?a :: ?b :: ?stk) ] =>
    rewrite lem_size_app;
    apply lem_exec_append_trans with
    (i' := size(l1)) (i'' := size(l2)) (s' := s) (stk' := b :: stk);
    scrush
  | [ H1 : exec ?l1 (0,?s,?stk) (size(?l1), ?s, ?stk1),
      H2 : exec ?l2 (0,?s,?stk1) (size(?l2) + ?i, ?s, ?stk2)
      |- exec (?l1 ++ ?l2) (0,?s,?stk) (size(?l1 ++ ?l2) + ?i, ?s, ?stk2) ] =>
    rewrite lem_size_app;
    apply lem_exec_append_trans with
    (i' := size(l1)) (i'' := size(l2) + i) (s' := s) (stk' := stk1);
    try omega; ycrush; scrush
  end;
  clear H_exec_append_tac.

(* Compilation *)

Fixpoint acomp (a : aexpr) : list instr :=
  match a with
  | Anum n => LOADI n :: nil
  | Avar x => LOAD x :: nil
  | Aplus a1 a2 => acomp a1 ++ acomp a2 ++ (ADD :: nil)
  end.

Lemma lem_acomp_correct :
  forall a s stk, exec (acomp a) (0,s,stk) (size(acomp a),s, aval s a :: stk).
Proof.
  induction a; sauto.
  - exec_tac.
  - exec_tac.
  - assert (exec (acomp a1 ++ acomp a2) (0,s,stk)
                 (size(acomp a1 ++ acomp a2),s,aval s a2 :: aval s a1 :: stk)) by exec_append_tac.
    assert (exec (ADD :: nil) (0,s,aval s a2 :: aval s a1 :: stk) (1,s,(aval s a1 + aval s a2) :: stk)) by
        exec_tac.
    assert (forall l, size l - size l = 0) by (intro; omega);
    assert (HH: exec ((acomp a1 ++ acomp a2) ++ ADD :: nil) (0, s, stk)
                     (size ((acomp a1 ++ acomp a2) ++ ADD :: nil), s, aval s a1 + aval s a2 :: stk)) by
        (apply lem_exec_append_trans with
         (i' := size(acomp a1 ++ acomp a2)) (s' := s) (stk' := aval s a2 :: aval s a1 :: stk) (i'' := 1);
         solve [ sauto | ycrush | rewrite lem_size_app; scrush ]).
    clear -HH; scrush.
Qed.

Lemma lem_acomp_append :
   forall a1 a2 s stk, exec (acomp a1 ++ acomp a2) (0, s, stk)
                            (size (acomp a1 ++ acomp a2), s, aval s a2 :: aval s a1 :: stk).
Proof.
  pose lem_acomp_correct; exec_append_tac.
Qed.

Fixpoint bcomp (b : bexpr) (f : bool) (n : Z) : list instr :=
  match b with
  | Bval v => if eqb v f then JMP n :: nil else nil
  | Bnot b' => bcomp b' (negb f) n
  | Band b1 b2 =>
    let cb2 := bcomp b2 f n in
    let m := if f then size cb2 else size cb2 + n in
    let cb1 := bcomp b1 false m in
    cb1 ++ cb2
  | Bless a1 a2 =>
    acomp a1 ++ acomp a2 ++ (if f then JMPLESS n :: nil else JMPGE n :: nil)
  end.

Lemma lem_bcomp_correct :
  forall b f n s stk, 0 <= n ->
                      exec (bcomp b f n) (0,s,stk)
                           (size(bcomp b f n) + (if eqb f (bval s b) then n else 0),s,stk).
Proof.
  induction b; simpl; intros f n s stk H.
  - sauto; try exec_tac;
      Reconstr.hsimple Reconstr.AllHyps
                       (@Coq.Bool.Bool.eqb_false_iff, @Coq.Bool.Bool.eqb_prop)
                       Reconstr.Empty.
  - assert (HH: (if eqb f (negb (bval s b)) then n else 0) =
                (if eqb (negb f) (bval s b) then n else 0)) by
        Reconstr.hsimple Reconstr.Empty
                         (@Coq.Bool.Bool.eqb_negb2, @Coq.Bool.Bool.negb_false_iff,
                          @Coq.Bool.Bool.negb_true_iff, @Coq.Bool.Bool.no_fixpoint_negb,
                          @Coq.Bool.Bool.negb_involutive, @Coq.Bool.Bool.diff_true_false,
                          @Coq.Bool.Bool.eqb_false_iff, @Coq.Bool.Bool.eqb_prop)
                         (@Coq.Bool.Bool.eqb, @Coq.Init.Datatypes.negb).
    rewrite HH; clear HH.
    scrush.
  - pose (m := if f then size (bcomp b2 f n) else size (bcomp b2 f n) + n); fold m.
    assert (H0: 0 <= m) by
        (unfold m; clear -H; sauto; unfold size; omega).
    destruct (bval s b1) eqn:H1; simpl.
    + apply lem_exec_append_trans with
      (i' := size (bcomp b1 false m))
        (s' := s) (stk' := stk)
        (i'' := size (bcomp b2 f n) + (if eqb f (bval s b2) then n else 0)).
      * generalize (IHb1 false m s stk); scrush.
      * auto with zarith.
      * assert (HH: size (bcomp b1 false m) - size (bcomp b1 false m) = 0) by omega.
        rewrite HH; clear HH.
        auto.
      * rewrite lem_size_app; auto with zarith.
    + rewrite lem_size_app.
      assert (HH: size (bcomp b2 f n) + (if eqb f false then n else 0) = m) by
          (unfold m; destruct f; simpl; omega).
      rewrite <- ZArith.BinInt.Z.add_assoc; rewrite HH; clear HH.
      apply lem_exec_appendR.
      assert (HH: size (bcomp b1 false m) + m =
                  size (bcomp b1 false m) + if eqb false (bval s b1) then m else 0) by scrush.
      rewrite HH; clear HH.
      auto.
  - assert (HH: aval s a >=? aval s a0 = negb (aval s a <? aval s a0)) by
        Reconstr.htrivial Reconstr.Empty
                          (@Coq.ZArith.BinInt.Z.geb_leb, @Coq.Bool.Bool.negb_true_iff,
                           @Coq.ZArith.BinInt.Z.leb_antisym)
                          Reconstr.Empty.
    assert (exec (if f then JMPLESS n :: nil else JMPGE n :: nil) (0, s, aval s a0 :: aval s a :: stk)
                 (size (if f then JMPLESS n :: nil else JMPGE n :: nil) +
                  (if eqb f (aval s a <? aval s a0) then n else 0), s, stk)) by
        (sauto; exec_tac).
    clear HH.
    assert (HH: forall (l1 l2 l3 : list instr), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3) by scrush.
    repeat rewrite HH; clear HH.
    pose proof (lem_acomp_append a a0 s stk).
    exec_append_tac.
Qed.
