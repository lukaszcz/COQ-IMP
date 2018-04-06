Require Import AExp Com Big_Step Hoare.
Require Import String.
Local Open Scope Z_scope.


Fixpoint sum (i: Z): Z := if (Z.leb i 0) then 0 else (i * (i + 1))/2.


Definition wsum (x y: string) :=
Com.While (less (Anum 0) (Avar x))
(Com.Seq
 (Com.Assign y (Aplus (Avar y) (Avar x))) 
 (Com.Assign x (Aplus (Avar y) (Anum (-1))))).

Lemma se: forall n x y, x <> y -> hoare (fun s => s x = n) (Com.Seq (Com.Assign y (Anum 0)) (wsum x y)) (fun s => s y = sum n).
Proof. intros n x y Hn.
       specialize (Hoare.Seq (fun s : state => s x = n) (fun s : state => s y =  sum n - sum (s x)) 
                             (fun s : state => s y = sum n)); intros.
       apply H.
       Focus 2.
       specialize (While' (less (Anum 0) (Avar x)) (fun s : state => s y =  sum n - sum (s x))
                           (fun s : state => s y = sum n)); intros.
       apply H0.
       eapply Hoare.Seq.
       Reconstr.scrush (** hammer *).
       eapply Assign'. intros.
       unfold state_subst. cbn in *.
       destruct H1. rewrite H1.
       unfold update.
       case_eq (string_dec x y); case_eq (string_dec x x); intros.
       simpl. subst. now rewrite H1 at 1.
       contradiction.
       simpl. rewrite <- H1.
       simpl. admit.
       contradiction.
       intros.
       destruct H1.
       rewrite lem_bval_less in H2.
       cbn in *.
       rewrite Z.ltb_antisym in H2.
       assert ( (s x <=? 0) = true).
       { Reconstr.hsimple (@H2)
		      Reconstr.Empty
		      (@AExp.val, @AExp.state, @Coq.Init.Datatypes.negb) (** hammer *). }
       assert (sum (s x) = 0).
       { Reconstr.hsimple (@H3)
		        (@Coq.Bool.Bool.not_true_iff_false)
		        (@AExp.state, @sum, @AExp.val) (** hammer *). }
       rewrite H4 in H1.
       assert (sum n - 0 = sum n).
       { Reconstr.scrush (** hammer *). }
       now rewrite H5 in H1.
       eapply Assign'.
       intros. unfold state_subst, update.
       case_eq ( string_dec y y ); case_eq ( string_dec y x ); intros.
       simpl. Reconstr.scrush (** hammer *). 
       simpl. rewrite H0. 
       now rewrite (Zminus_diag_reverse (sum n)).
       simpl. contradiction.
       simpl. contradiction.
Admitted.

Lemma while_sum: forall s t x y, big_step (wsum x y, s) t -> t y = s y + sum (s x).
Proof. Admitted.

Lemma sum_via_bigstep: forall s t x y, big_step ((Com.Seq (Com.Assign y (Anum 0)) (wsum x y)), s) t -> t y = sum (s x).
Proof. Admitted.

(** todos *)
(** remove the admits above *)
