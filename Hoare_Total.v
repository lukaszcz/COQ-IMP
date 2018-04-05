Require Import AExp Com Big_Step Hoare.
Require Import String.

Definition hoaret_valid (P: assn) (c: com) (Q: assn): Prop :=
  forall s, P s -> (exists t, big_step (c, s) t /\ Q t ).

Inductive hoaret: assn -> com -> assn -> Prop :=
  | Skip  : forall P c, hoaret P c P
  | Assign: forall P a x, hoaret (fun s => P (state_subst s a x)) (Com.Assign x a) P
  | Seq   : forall P Q R c1 c2, hoaret P c1 Q -> hoare Q c2 R -> hoaret P (Com.Seq c1 c2) R
  | If    : forall P Q b c1 c2, hoaret (fun s => P s /\ bval s b = true)  c1 Q ->
                                  hoaret (fun s => P s /\ bval s b = false) c2 Q -> hoaret P (Com.If b c1 c2) Q
  | While : forall P b c (T: state -> nat -> Prop),
                 (forall n, hoaret (fun s => P s /\ bval s b = true /\ (T s n)) c (fun s => P s /\ (exists n', n' < n /\ (T s n')))) ->
                 hoaret P (Com.While b c) (fun s => P s /\ bval s b = false)
  | conseq: forall (P P' Q Q': assn) c, (entails P' P) -> hoaret P c Q -> (entails Q Q') -> hoaret P' c Q'.

Lemma While_fun: forall b (P Q: assn) c (f: state -> nat), 
                   (forall n: nat, hoaret (fun s => P s /\ bval s b = true /\ n = f s) c (fun s => P s /\ f s < n)) ->
                   hoaret P (Com.While b c) (fun s => P s /\ bval s b = false).
Proof. intros.
       specialize (While P b c (fun s n => n = f s)); intros.
       apply H0. intros.
       eapply conseq.
       - Reconstr.scrush (** hammer *).
       - Reconstr.scrush (** hammer *).
	     - Reconstr.hobvious Reconstr.Empty
		     Reconstr.Empty
		    (@Hoare.entails) (** hammer *).
Qed.

Lemma strengthen_pre: forall (P P' Q: assn) c, (entails P' P) -> hoaret P c Q -> hoaret P' c Q.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@conseq)
		(@Hoare.entails) (** hammer *).
Qed.

Lemma weaken_post: forall (P Q Q': assn) c, (entails Q Q') -> hoaret P c Q -> hoaret P c Q'.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@conseq)
		(@Hoare.entails) (** hammer *).
Qed.

Lemma Assign': forall (P Q: assn) a x, (forall s, P s -> Q (state_subst s a x)) -> hoaret P (Com.Assign x a) Q.
Proof. intros.
       specialize (strengthen_pre (fun s: state => Q (state_subst s a x)) P Q  (Com.Assign x a) ); intros.
       Reconstr.scrush (** hammer *).
Qed.

Lemma While_fun': forall b (P Q: assn) c (f: state -> nat), 
                 (forall n: nat, hoaret (fun s => P s /\ bval s b = true /\ n = f s) c (fun s => P s /\ f s < n)) ->
                 (forall s, P s /\ bval s b = false -> Q s) ->
                 hoaret P (Com.While b c) Q.
Proof. intros.
       specialize (While P b c (fun s n => n = f s)); intros.
       specialize (weaken_post P (fun s : state => P s /\ bval s b = false) Q (Com.While b c)); intros.
       apply H2.
       Reconstr.scrush (** hammer *).
       apply H1. intros.
       eapply conseq.
      - Reconstr.scrush (** hammer *).
      - Reconstr.scrush (** hammer *).
      - Reconstr.hobvious Reconstr.Empty
		      Reconstr.Empty
		      (@entails) (** hammer *).
Qed.

(** todos *)
(** put the standard example *)
(** prove soundness and completeness: this may take time..! *)

Lemma hoaret_sound: forall P Q c, hoaret P c Q -> hoaret_valid P c Q.
Proof. unfold hoare_valid. intros P Q c h.
       induction h; try yelles 2.
Admitted.








