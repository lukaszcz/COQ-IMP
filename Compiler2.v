Require Import Com.
Require Import Big_Step.
Require Import Star.
Require Import Compiler.
Require Import List.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import ListNotations.

Fixpoint exec_n (l: list instr) (c1: config) (n: nat) (c2: config): Prop :=
  match n with
    | O   => c1 = c2
    | S m => exists c', (exec1 l c1 c') /\ (exec_n l c' m c2)
  end.

Definition isuccs (i: instr) (n: Z): list Z :=
  match i with
    | JMP j     => [n + 1 + j]
    | JMPLESS j => [n + 1 + j; n + 1]
    | JMPGE j   => [n + 1 + j; n + 1]
    | _         => [n + 1]
  end.

Definition succs (P: list instr) (n: Z)  
                 (exprf: { i: Z & (Z.le i 0) /\ (Nat.lt (Z.to_nat i) (List.length P))}): list Z :=
  isuccs (znth (projT1 exprf) P ADD) n.

Fixpoint eqb_instr (i1 i2: instr): bool :=
  match i1, i2 with
    | JMP _, JMP _ 
    | LOAD _, LOAD _
    | LOADI _, LOADI _
    | ADD, ADD
    | STORE _, STORE _
    | JMPLESS _, JMPLESS _
    | JMPGE _, JMPGE _ => true
    | _, _ => false
  end.

Fixpoint is_in (a: instr) (l: list instr) : bool :=
  match l with
    | [] => false
    | b :: m => eqb_instr b a || is_in a m
  end.

Fixpoint is_in_Z (a: Z) (l: list Z) : bool :=
  match l with
    | [] => false
    | b :: m => Z.eqb b a || is_in_Z a m
  end.

Fixpoint seqZ (start:Z) (len:nat) : list Z :=
  match len with
    | O => nil
    | S len => start :: seqZ (Z.succ start) len
  end.

Definition _exists (P: list instr)
                   (exprf: { i: Z & (Z.le i 0) /\ (Nat.lt (Z.to_nat i) (List.length P))}): list Z :=
  let l1   := succs P 0 exprf in
  let l2   := seqZ 0 (List.length P) in
  (List.filter ( fun a => negb (is_in_Z a l1)) l2).

Lemma exec_0: forall P c, exec_n P c 0 c.
Proof. scrush. Qed.

Lemma exec_n_exec: forall n P c1 c2, exec_n P c1 n c2 -> exec P c1 c2.
Proof. unfold exec. intro n. 
       induction n; intros.
       scrush.
       destruct H.
       eapply @star_step with (y := x). easy.
       apply IHn. easy.
Qed.

Lemma exec_Suc: forall n P c1 c2 c3, exec P c1 c2 -> exec_n P c2 n c3 -> exec_n P c1 (S n) c3.
Proof. Admitted.

Lemma exec_exec_n: forall n P c1 c2, exec P c1 c2 -> exec_n P c1 n c2.
Proof. Admitted.

(** go through the whole file..! *)








