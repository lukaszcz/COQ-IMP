Require Import Com.
Require Import Big_Step.
Require Import Star.
Require Import Compiler.
Require Import List String.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import ListNotations.

Fixpoint is_in_Z (a: Z) (l: list Z) : bool :=
  match l with
    | [] => false
    | b :: m => Z.eqb b a || is_in_Z a m
  end.

Fixpoint remove_dupsZ (l: list Z) :=
  match l with
    | [] => []
    | x :: xs => if (is_in_Z x xs) then remove_dupsZ xs else x :: remove_dupsZ xs
  end.

Fixpoint exec_n (l: list instr) (c1: config) (n: nat) (c2: config): Prop :=
  match n with
    | O   => c1 = c2
    | S m => exists c', (exec1 l c1 c') /\ (exec_n l c' m c2)
  end.

Definition _isuccs (i: instr) (n: Z): list Z  :=
  match i with
    | JMP j     => [n + 1 + j]
    | JMPLESS j => [n + 1 + j; n + 1]
    | JMPGE j   => [n + 1 + j; n + 1]
    | _         => [n + 1]
  end.

Definition isuccs i n := remove_dupsZ (_isuccs i n).

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
Proof. intros.
       induction a; intros.
       simpl.
       now repeat rewrite eqb_reflx.
Qed.

Fixpoint string_eqb (x y: string) :=
  match x, y with
    | ""%string, ""%string => true
    | String a s1, String b s2 => 
      if ascii_eqb a b then
      string_eqb s1 s2 else false 
    | _, _ => false
  end.

Lemma string_eqb_refl: forall x, string_eqb x x = true.
Proof. intros.
       induction x; intros.
       - now simpl. 
       - simpl. now rewrite ascii_eqb_refl.
Qed.


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

Definition succs (P: list instr) (n: Z)
                 (exprf: { i: Z | (Z.le 0 i) /\ (i < size P)}): list Z :=
 isuccs (znth (proj1_sig exprf) P ADD) (n + (proj1_sig exprf)).

Fixpoint seq (start:Z) (len:nat): list Z :=
  match len with
    | O => nil
    | S len => start :: seq (Z.succ start) len
  end.

Definition seqZ (n: Z) (m: nat) := seq n (Z.to_nat ((Z.of_nat m) - n)).

Definition exits (P: list instr) exprf: list Z :=
  let l1   := succs P 0 exprf in
  let l2   := seqZ 0 (List.length P) in
  (List.filter (fun a => negb (is_in_Z a l1)) l2).

Section BP_term_exec_n.

Lemma exec_0: forall P c, exec_n P c 0 c.
Proof. scrush. Qed.

Lemma exec_n_exec: forall n P c1 c2, exec_n P c1 n c2 -> exec P c1 c2.
Proof. unfold exec. intro n. 
       induction n; intros.
       scrush.
       destruct H.
       eapply @star_step with (y := x); scrush.
Qed.

Lemma exec1_exec_n: forall P c1 c2, exec1 P c1 c2 <-> exec_n P c1 1 c2.
Proof. scrush. Qed.

Lemma exec_trans: forall P c1 c2 c3, exec P c1 c2 -> exec P c2 c3 -> exec P c1 c3.
Proof. intros.
       revert c3 H0.
       induction H; intros;
       [ scrush |
        	Reconstr.hobvious (@H, @H1, @IHstar)
		     (@Star.star_step)
		     (@Compiler.exec) (** *hammer *)].
Qed.

Lemma exec_Suc: forall n P c1 c2 c3, exec1 P c1 c2 -> exec_n P c2 n c3 -> exec_n P c1 (S n) c3.
Proof. intros. simpl.
       exists c2. scrush.
Qed.

Lemma exec_exec_n: forall P c1 c2, exec P c1 c2 -> exists n, exec_n P c1 n c2.
Proof. intros.
       induction H; intros.
       - exists O. scrush.
       - destruct IHstar as (n, IH).
         exists (S n). apply exec_Suc with (c2 := y); scrush.
Qed.

Lemma exec_equiv_exec_n: forall P c1 c2, exec P c1 c2 <-> exists n, exec_n P c1 n c2.
Proof. intros. split.
       intros; now eapply exec_exec_n in H.
       intros. destruct H. now eapply exec_n_exec in H.
Qed.


Lemma exec_n_Nil_l: forall k c1 c2, exec_n [] c1 k c2 -> (c1 = c2 /\ k = O).
Proof. intro k.
       induction k; intros; scrush.
Qed.

Lemma exec_n_Nil_r: forall k c1 c2, (c1 = c2 /\ k = O) -> exec_n [] c1 k c2.
Proof. intro k.
       induction k; intros; scrush.
Qed.

Lemma exec_n_Nil: forall k c1 c2, exec_n [] c1 k c2 <-> (c1 = c2 /\ k = O).
Proof. pose exec_n_Nil_l; pose exec_n_Nil_r; scrush. Qed.

Lemma exec_n_step_l: forall k n n' P s s' stk stk',
  n <> n' -> 
  exec_n P (n, stk, s) k (n', stk', s') -> exists c, exec P (n, stk, s) c /\ exec_n P c (k - 1) (n', stk', s') /\ Nat.lt 0%nat k.
Proof. intro k.
       induction k; intros.
       - cbn in *.
         exists (n', stk', s'); scrush.
       - cbn in *. destruct H0. exists x. split.
         destruct H0.
         unfold exec.
         eapply @star_step with (z := x) in H0. 
         scrush.
         scrush.
         assert ((k - 0)%nat = k) by scrush.
         rewrite H1. split.
         scrush.

	     Reconstr.htrivial Reconstr.Empty
		   (@Coq.Arith.PeanoNat.Nat.lt_0_succ, @Coq.Arith.PeanoNat.Nat.le_succ_l)
		   (@Coq.Arith.PeanoNat.Nat.lt); Reconstr.scrush (** hammer *).
Qed.


Lemma exec1_n_step_l: forall k n n' P s s' stk stk',
  n <> n' -> 
  exec_n P (n, stk, s) k (n', stk', s') -> exists c, exec1 P (n, stk, s) c /\ exec_n P c (k - 1) (n', stk', s') /\ Nat.lt 0%nat k.
Proof. intro k.
       induction k; intros.
       - cbn in *.
         exists (n', stk', s'); scrush.
       - cbn in *. destruct H0. exists x.
         destruct H0. split. scrush.
         split. scrush.
	       Reconstr.htrivial Reconstr.Empty
		     (@Coq.Arith.PeanoNat.Nat.lt_0_succ)
		     (@Coq.Arith.PeanoNat.Nat.lt); scrush.
Qed.


Lemma exec_n_step_r: forall k n n' P s s' stk stk',
  n <> n' -> 
  (exists c, exec1 P (n, stk, s) c /\ exec_n P c (k - 1) (n', stk', s') /\ Nat.lt 0%nat k) ->
   exec_n P (n, stk, s) k (n', stk', s').
Proof. intros.
       case_eq k; intros.
       - destruct H0, H0, H2. subst.
         contradict H3. scrush.
       - simpl. destruct H0, H0, H2.
         exists x. split. easy.
         assert ((S n0 - 1)%nat = n0) by scrush. subst.
         now rewrite <- H4.
Qed.

End BP_term_exec_n.

Section CSES.

Lemma exec_n_step: forall k n n' P s s' stk stk',
  n <> n' ->
  (exists c, exec1 P (n, stk, s) c /\ exec_n P c (k - 1) (n', stk', s') /\ Nat.lt 0%nat k) <-> 
  exec_n P (n, stk, s) k (n', stk', s').
Proof. split; intros. 
       pose exec_n_step_r; scrush.
       pose exec1_n_step_l; scrush.
Qed.

Lemma execn_end: forall k n n' P s s' stk stk',
  size P <= n -> exec_n P (n, s, stk) k (n', s', stk') -> (n' = n /\ stk' = stk /\ s' = s /\ k = 0%nat).
Proof. intro k.
       induction k; intros.
       - cbn in *; scrush.
       - cbn in *.
         destruct H0, H0.
	       Reconstr.hcrush (@H0, @H)
		        (@Coq.ZArith.BinInt.Z.lt_nge, @Coq.ZArith.BinInt.Z.gt_lt_iff)
		        Reconstr.Empty.
Qed.


Lemma exec1_end: forall P c1 c2, size P <= (fst (fst c1)) -> (exec1 P c1 c2 -> False).
Proof. intros.
       destruct c1, p.
       cbn in *. unfold exec1 in *.
       destruct H0, H0, H0, H0.
       inversion H0. subst.
       destruct H1, H2.
       assert ((size P <= x) -> (x < size P) -> False).
       { Reconstr.hobvious (@H, @H3)
	       (@Coq.ZArith.BinInt.Z.lt_nge)
		     Reconstr.Empty.
       } scrush.
Qed.

End CSES.

Section BP_term_succs.

Lemma succs_simps: forall n v x i p, succs [ADD] n p       = remove_dupsZ [n + 1]            /\
                                     succs [LOADI v] n p   = remove_dupsZ [n + 1]            /\
                                     succs [LOAD x] n p    = remove_dupsZ [n + 1]            /\
                                     succs [STORE x] n p   = remove_dupsZ [n + 1]            /\
                                     succs [JMP i] n p     = remove_dupsZ [n + 1 + i]        /\
                                     succs [JMPGE i] n p   = remove_dupsZ [n + 1 + i; n + 1] /\
                                     succs [JMPLESS i] n p = remove_dupsZ [n + 1 + i; n + 1].
Proof. intros; destruct p; 
       unfold succs; cbn in *;
       destruct a;
       assert (x0 = 0).
	     { Reconstr.htrivial (@H, @H0)
		     (@Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.BinInt.Z.le_refl, 
         @Coq.ZArith.BinInt.Z.le_antisymm, @Coq.ZArith.BinInt.Z.log2_up_nonpos, 
         @Coq.ZArith.BinInt.Z.log2_up_null, @Coq.ZArith.Znat.Z2Nat.inj_0, 
         @Coq.ZArith.Znat.Z2Nat.inj_succ, @Coq.ZArith.Znat.Z2Nat.inj_lt,
         @Coq.ZArith.BinInt.Z.one_succ) (@Coq.Arith.PeanoNat.Nat.lt); scrush.
        } rewrite H1; scrush.
Qed.

Lemma succs_empty: forall n p, succs [] n p = [].
Proof. intros; destruct p; unfold succs; cbn in *;
	     Reconstr.hobvious (@a)
		   (@Coq.ZArith.BinInt.Z.lt_nge, @Coq.ZArith.Znat.Z2Nat.inj_lt, @Coq.ZArith.BinInt.Z.le_refl)
		   Reconstr.Empty.
Qed.

Lemma succs_iexec1: forall P s stk c p, c = iexec (znth (proj1_sig p) P ADD) ((proj1_sig p), s, stk) ->
                                        List.In (fst (fst c)) (succs P 0 p).
Proof. intros; destruct c, p0, p; unfold succs, isuccs, _isuccs. cbn in *.
       case_eq (znth x P ADD ); intros; rewrite H0 in *;
       try scrush.
       case_eq (hd 0 (tl stk) <? hd 0 stk); intros; rewrite H1 in *; inversion H; try scrush.
       unfold remove_dupsZ.
       case_eq (is_in_Z (x + 1 + z0) [x + 1]); intros.
       inversion H2.
       assert ((x + 1 =? x + 1 + z0) = true). scrush.
       assert ((x + 1 = x + 1 + z0)).
       { Reconstr.htrivial (@H6)
	     	 (@Coq.ZArith.BinInt.Z.add_1_l, @Coq.ZArith.BinInt.Z.eqb_eq)
		     (@Coq.ZArith.BinIntDef.Z.succ).
       }  
       assert (z0 = 0).
       { Reconstr.hsimple (@H8)
		     (@Coq.ZArith.BinInt.Z.add_cancel_l, @Coq.ZArith.BinInt.Z.add_0_r)
		     Reconstr.Empty.
       } subst. cbn. scrush.
       cbn. now left.
       inversion H. 
       case_eq (hd 0 (tl stk) >=? hd 0 stk); intros; rewrite H1 in *.
       inversion H. cbn.
       case_eq ( (x + 1 =? x + 1 + z0)); intros.
       assert ((x + 1 = x + 1 + z0)).
       { Reconstr.htrivial (@H5)
	     	 (@Coq.ZArith.BinInt.Z.add_1_l, @Coq.ZArith.BinInt.Z.eqb_eq)
		     (@Coq.ZArith.BinIntDef.Z.succ).
       }
       assert (z0 = 0).
       { Reconstr.hsimple (@H9)
		     (@Coq.ZArith.BinInt.Z.add_cancel_l, @Coq.ZArith.BinInt.Z.add_0_r)
		     Reconstr.Empty.
       } subst. cbn. scrush.
       scrush.
       cbn.
       case_eq ((x + 1 =? x + 1 + z0)); intros.
       now left.
       right. scrush.
Qed.

Lemma In_Singleton: forall {A} (a b: A),  In a [b] -> a = b.
Proof. intros; destruct H; cbn in *; scrush. Qed.

Lemma succs_shift: forall P n k p, List.In (k - n) (succs P 0 p) -> List.In k (succs P n p).
Proof. intros.
       destruct p. cbn in *.
       unfold succs in *. cbn in *.
       unfold isuccs in *.
       case_eq (znth x P ADD ); intros; rewrite H0 in *.
       apply In_Singleton in H.
       assert (k = n + x + 1).
       { 	Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      Reconstr.Empty.
       } scrush.
       apply In_Singleton in H.
       assert (k = n + x + 1).
       { 	Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      Reconstr.Empty.
       } scrush.
       apply In_Singleton in H.
       assert (k = n + x + 1).
       { 	Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      Reconstr.Empty.
       } scrush.
       apply In_Singleton in H.
       assert (k = n + x + 1).
       { 	Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		      Reconstr.Empty.
       } scrush.
       apply In_Singleton in H.
       assert (k = n + x + 1 + z).
       { Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_simpl_r, @Coq.ZArith.BinInt.Zplus_minus)
		     Reconstr.Empty.
       } scrush.
       cbn in *.
       case_eq ((x + 1 =? x + 1 + z)); intros.
       assert ((x + 1 = x + 1 + z)).
       { Reconstr.htrivial (@H1)
		     (@Coq.ZArith.BinInt.Z.add_1_l, @Coq.ZArith.BinInt.Z.eqb_eq)
		     (@Coq.ZArith.BinIntDef.Z.succ).
       }
       assert (z = 0).
       { Reconstr.hsimple (@H2)
		     (@Coq.ZArith.BinInt.Z.add_cancel_l, @Coq.ZArith.BinInt.Z.add_0_r)
		      Reconstr.Empty; scrush.
       } subst. cbn.
       assert (n + x + 1 + 0 = n + x + 1).
       { scrush. }
       rewrite H3.
       assert ((n + x + 1 =? n + x + 1) = true).
       { Reconstr.htrivial Reconstr.Empty
		     (@Coq.ZArith.BinInt.Z.eqb_eq)
		     (@Coq.ZArith.BinIntDef.Z.succ); scrush.
       }
       rewrite H4. cbn.
       assert ((x + 1 =? x + 1 + 0) = true).
       { scrush. }
       rewrite H5 in *. cbn in *.
       assert (k = n + x + 1).
       { Reconstr.htrivial (@H)
		     (@Coq.ZArith.BinInt.Zplus_succ_r_reverse, @Coq.ZArith.BinInt.Zplus_minus)
		     (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).
       } scrush.
       rewrite H1 in *. cbn in *.
       assert ((n + x + 1 <> n + x + 1 + z)).
       { assert (x + 1 <> x + 1 + z).
         { Reconstr.hcrush (@H1)
	       	 (@Coq.ZArith.BinInt.Z.add_0_r, @Coq.ZArith.BinInt.Z.eqb_eq, @Coq.ZArith.BinInt.Z.add_cancel_l)
		       (@Coq.ZArith.BinIntDef.Z.succ).
         } unfold Logic.not in *. intros.  
         specialize (Coq.ZArith.BinInt.Z.add_cancel_l (x + 1) (x + 1 + z) n); intros.
         apply H2. apply H4.	
        Reconstr.htrivial (@H3)
		    (@Coq.ZArith.BinInt.Zplus_succ_r_reverse, @Coq.ZArith.BinInt.Zplus_assoc_reverse)
	      (@Coq.ZArith.BinIntDef.Z.succ).
       }
       assert ((n + x + 1 =? n + x + 1 + z) = false).
       { Reconstr.htrivial (@H2)
		     (@Coq.ZArith.BinInt.Z.eqb_neq)
		     Reconstr.Empty.
       }
       rename H2 into H2a.
       rename H3 into H2.
       rewrite H2. cbn.
       destruct H. left.
	     Reconstr.htrivial (@H)
		   (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_succ_r, @Coq.ZArith.BinInt.Z.add_simpl_r, @Coq.ZArith.BinInt.Zplus_minus)
		   (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).
       destruct H.
       right. left.
	     Reconstr.htrivial (@H) 
		   (@Coq.ZArith.BinInt.Z.add_succ_r, @Coq.ZArith.BinInt.Zplus_minus)
		   (@Coq.ZArith.BinIntDef.Z.succ, @Coq.ZArith.BinIntDef.Z.sub). scrush.

       cbn in *.
       case_eq ((x + 1 =? x + 1 + z)); intros; rewrite H1 in *; cbn in *.
       destruct H.
       assert ( (n + x + 1 =? n + x + 1 + z) = true).
       { Reconstr.hcrush (@H1)
		    (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_succ_r, @Coq.ZArith.BinInt.Z.eqb_eq, @Coq.ZArith.BinInt.Z.eqb_refl)
		    (@Coq.ZArith.BinIntDef.Z.succ).
       } rewrite H2. cbn. left. 
       Reconstr.htrivial (@H)
       (@Coq.ZArith.BinInt.Zplus_succ_r_reverse, @Coq.ZArith.BinInt.Zplus_minus)
       (@Coq.ZArith.BinIntDef.Z.succ, @Coq.ZArith.BinIntDef.Z.sub).
       scrush.
       assert ((n + x + 1 <> n + x + 1 + z)).
       { assert (x + 1 <> x + 1 + z).
         { Reconstr.hcrush (@H1)
	       	 (@Coq.ZArith.BinInt.Z.add_0_r, @Coq.ZArith.BinInt.Z.eqb_eq, @Coq.ZArith.BinInt.Z.add_cancel_l)
		       (@Coq.ZArith.BinIntDef.Z.succ).
         } unfold Logic.not in *. intros.  
         specialize (Coq.ZArith.BinInt.Z.add_cancel_l (x + 1) (x + 1 + z) n); intros.
         apply H2. apply H4.	
        Reconstr.htrivial (@H3)
		    (@Coq.ZArith.BinInt.Zplus_succ_r_reverse, @Coq.ZArith.BinInt.Zplus_assoc_reverse)
	      (@Coq.ZArith.BinIntDef.Z.succ).
       }
       assert ((n + x + 1 =? n + x + 1 + z) = false).
       { Reconstr.htrivial (@H2)
		     (@Coq.ZArith.BinInt.Z.eqb_neq)
		      Reconstr.Empty. }
       rename H2 into H2a.
       rename H3 into H2.
       rewrite H2. cbn.
       destruct H. left.
	     Reconstr.htrivial (@H)
		   (@Coq.ZArith.BinInt.Zplus_assoc_reverse, @Coq.ZArith.BinInt.Z.add_succ_r, 
        @Coq.ZArith.BinInt.Z.add_simpl_r, @Coq.ZArith.BinInt.Zplus_minus)
		   (@Coq.ZArith.BinIntDef.Z.sub, @Coq.ZArith.BinIntDef.Z.succ).
       destruct H. right.
	     Reconstr.htrivial (@H)
		   (@Coq.ZArith.BinInt.Z.add_succ_r, @Coq.ZArith.BinInt.Zplus_minus)
		   (@Coq.ZArith.BinIntDef.Z.succ, @Coq.ZArith.BinIntDef.Z.sub).
       scrush.
Qed.

Lemma prf_cons: forall (x: instr) (xs: list instr), 
{i : Z | 0 <= i /\ i < (size xs)} -> 
{i : Z | 0 <= i /\ i < (size (x :: xs))}.
Proof. intros. destruct H. exists x0; unfold size in *; cbn in *;
     	 Reconstr.hobvious (@a)
		  (@Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.Znat.Zpos_P_of_succ_nat)
		  (@Coq.ZArith.BinInt.Z.lt, @Coq.ZArith.BinInt.Z.le, @Compiler.size).
Defined.

Lemma succs_Cons: forall x xs n p,
succs (x :: xs) n (prf_cons x xs p) = remove_dupsZ (isuccs x n ++ succs xs (n + 1) p).
Proof. Admitted.

Lemma acomp_succs: forall a (n: Z) p, succs (acomp a) n p = seqZ n (Z.to_nat n + (List.length (acomp a))).
Proof. Admitted.

Lemma helper: forall (xs ys: list instr) a,
   a < size ys ->
   a < size (xs ++ ys).
Proof. intro xs.
       induction xs; intros.
       - now cbn.
       - Reconstr.hsimple (@IHxs, @H)
		     (@Coq.ZArith.BinInt.Z.lt_succ_r, @Coq.ZArith.Znat.Zpos_P_of_succ_nat, 
          @Coq.Lists.List.app_length, @Coq.ZArith.BinInt.Z.lt_eq_cases)
		      (@Compiler.size).
Qed.

Lemma prf_concat: forall (xs ys: list instr),
{i : Z | 0 <= i /\ i < size ys} ->
{i : Z | 0 <= i /\ i < size (xs ++ ys)}. 
Proof. intros. destruct H. exists x. split. easy.
       destruct a. now apply helper.
Defined.

Lemma succs_append: forall xs ys n p q, succs (xs ++ ys) n (prf_concat xs ys p) = succs xs n q ++ succs ys (n + size xs) p.
Proof. Admitted.

(** go through the whole file..! *)


End BP_term_succs.


