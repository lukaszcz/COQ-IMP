(* Stack Machine and Compilation *)

Require Import imports.
Require Import AExp.
Local Open Scope Z_scope.

Inductive instr :=
| LOADI : val -> instr
| LOAD : vname -> instr
| ADD : instr.

Definition stack := list val.

Definition exec1 (i : instr) (s : state) (stk : stack) : stack :=
  match i with
  | LOADI n => n :: stk
  | LOAD x => s x :: stk
  | ADD => (hd 0 (tl stk) + hd 0 stk) :: (tl (tl stk))
  end.

Fixpoint exec (lst : list instr) (s : state) (stk : stack) : stack :=
  match lst with
  | nil => stk
  | i :: lst2 => exec lst2 s (exec1 i s stk)
  end.

Lemma lem_exec_append :
  forall is1 is2 s stk, exec (is1 ++ is2) s stk = exec is2 s (exec is1 s stk).
Proof.
  induction is1; sauto.
Qed.

(* Compilation *)

Fixpoint comp (a : aexpr) : list instr :=
  match a with
  | Anum n => LOADI n :: nil
  | Avar x => LOAD x :: nil
  | Aplus a1 a2 => comp a1 ++ comp a2 ++ (ADD :: nil)
  end.

Lemma lem_exec_comp : forall a s stk, exec (comp a) s stk = aval s a :: stk.
Proof.
  induction a; hauto q: on use: lem_exec_append.
Qed.
