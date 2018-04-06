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

Lemma exec_n_exec: forall n P c1 c2, exec_n P c1 n c2 -> (exec P) c1 c2.
Proof. unfold exec. intro n.
      induction n; sauto.
Admitted.

Definition isuccs (i: instr) (n: Z): list Z :=
  match i with
    | JMP j     => [n + 1 + j]
    | JMPLESS j => [n + 1 + j; n + 1]
    | JMPGE j   => [n + 1 + j; n + 1]
    | _         => [n + 1]
  end.


Parameter i: Z.
Parameter def: instr.

Definition succs (P: list instr) (n: Z): list Z :=
  let cond := (Z.leb i 0) && (Nat.ltb (Z.to_nat i) (List.length P)) in
  let s    := if cond then isuccs (znth i P def) n else [] in
  s.

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

Definition _exists (P: list instr): list Z :=
  let l1   := succs P 0 in
  let l2   := seqZ 0 (List.length P) in
  (List.filter ( fun a => negb (is_in_Z a l1)) l2).

(** go through the whole file..! *)








