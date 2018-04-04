
Require Import imports.

Inductive star {A : Type} (r : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star r x x
| star_step : forall x y z, r x y -> star r y z -> star r x z.

Lemma lem_star_trans {A} (r : A -> A -> Prop) :
  forall x y z, star r x y -> star r y z -> star r x z.
Proof.
  intros x y z H; revert z.
  induction H; sauto.
  Reconstr.hobvious Reconstr.AllHyps
		    (@star_step)
		    Reconstr.Empty.
Qed.

Lemma star_step1 {A} (r : A -> A -> Prop) :
  forall x y, r x y -> star r x y.
Proof.
  Reconstr.hobvious Reconstr.Empty
		    (@star_step, @star_refl)
		    Reconstr.Empty.
Qed.
