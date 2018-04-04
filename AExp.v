(* Arithmetic expressions *)

Require Import imports.
Require Import String.
Local Open Scope Z_scope.

Definition vname := string.
Definition val := Z.

Inductive aexpr :=
| Anum : val -> aexpr
| Avar : vname -> aexpr
| Aplus : aexpr -> aexpr -> aexpr.

Definition state := vname -> val.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Anum n => n
  | Avar x => s x
  | Aplus x y => aval s x + aval s y
  end.

Fixpoint asimp_const (e : aexpr) :=
  match e with
  | Anum n => Anum n
  | Avar x => Avar x
  | Aplus e1 e2 =>
    match asimp_const e1, asimp_const e2 with
    | Anum n1, Anum n2 => Anum (n1 + n2)
    | e1', e2' => Aplus e1' e2'
    end
  end.

Lemma lem_aval_asimp_const : forall s e, aval s (asimp_const e) = aval s e.
Proof.
  induction e; sauto.
Qed.

Fixpoint plus (e1 e2 : aexpr) :=
  match e1, e2 with
  | Anum n1, Anum n2 => Anum (n1 + n2)
  | Anum 0, _ => e2
  | _, Anum 0 => e1
  | _, _ => Aplus e1 e2
  end.

Lemma lem_aval_plus : forall s e1 e2, aval s (plus e1 e2) = aval s e1 + aval s e2.
Proof.
  induction e1; sauto.
Qed.

Fixpoint asimp (e : aexpr) :=
  match e with
  | Aplus x y => plus (asimp x) (asimp y)
  | _ => e
  end.

Lemma lem_aval_asimp : forall s e, aval s (asimp e) = aval s e.
Proof.
  induction e; sauto.
  Reconstr.htrivial Reconstr.AllHyps
                    (@lem_aval_plus)
                    Reconstr.Empty.
Qed.
