Require Import AExp Com Big_Step.
Require Import String.


Definition assn := state -> Prop.

Definition hoare_valid (P: assn) (c: com) (Q: assn): Prop :=
  forall s t, P s /\ big_step (c, s) t -> Q t.

Definition state_subst (s: state) (a: aexpr) (x: string): state := (update s x (aval s a)).
Definition entails (P Q: assn): Prop := forall s, P s -> Q s.

Inductive hoare: assn -> com -> assn -> Prop :=
  | Skip  : forall P c, hoare P c P
  | Assign: forall P a x, hoare (fun s => P (state_subst s a x)) (Assign x a) P
  | Seq   : forall P Q R c1 c2,  hoare P c1 Q -> hoare Q c2 R -> hoare P (Seq c1 c2) R
  | If    : forall P Q b c1 c2,  hoare (fun s => P s /\ bval s b = true)  c1 Q ->
                                 hoare (fun s => P s /\ bval s b = false) c2 Q -> hoare P (If b c1 c2) Q
  | While : forall P b c, hoare (fun s => P s /\ bval s b = true) c P ->
                          hoare P (While b c) (fun s => P s /\ bval s b = false)
  | conseq: forall (P P' Q Q': assn) c, (entails P' P) -> hoare P c Q -> (entails Q Q') -> hoare P' c Q'.


Lemma strengthen_pre: forall (P P' Q: assn) c, (entails P' P) -> hoare P c Q -> hoare P' c Q.
Proof.
	Reconstr.hsimple Reconstr.Empty
		(@conseq)
		(@entails) (** hammer *).
Qed.

Lemma weaken_post: forall (P Q Q': assn) c, (entails Q Q') -> hoare P c Q -> hoare P c Q'.
Proof.
	Reconstr.hobvious Reconstr.Empty
		(@conseq)
		(@entails) (** hammer *).
Qed.

Lemma Assign': forall (P Q: assn) a x, (forall s, P s -> Q (state_subst s a x)) -> hoare P (Com.Assign x a) Q.
Proof. intros.
       specialize (strengthen_pre (fun s: state => Q (state_subst s a x)) P Q  (Com.Assign x a) ); intros.
       Reconstr.scrush (** hammer *).
Qed.

Lemma While': forall b (P Q: assn) c, hoare (fun s => P s /\ bval s b = true) c P ->
                                      (forall s, P s /\ bval s b = false -> Q s) ->
                                      hoare P (Com.While b c) Q.
Proof. intros.
       specialize (While _ _ _ H); intros.
       specialize (weaken_post P (fun s : state => P s /\ bval s b = false) Q (Com.While b c)); intros.
       Reconstr.scrush (** hammer *).
Qed.

(** completeness of partial Hoare Logic *)

Lemma helper: forall c (P Q: assn), (forall s t, P s -> big_step (c, s) t -> Q t) -> hoare P c Q.
Proof. intro c.
       induction c; sauto.
       - Reconstr.heasy (@H)
		     (@weaken_post, @Skip, @Big_Step.SkipSem)
		     (@entails).
       - apply Assign'. Reconstr.scrush (** hammer *).
       - hammer. admit.
       - apply If. apply IHc1. intros.
         apply H with (s := s) (t := t). easy.
         apply IfTrue. easy. easy.
         apply IHc2. intros. apply H with (s := s) (t := t).
         easy. apply IfFalse; easy.
       - apply While'. eapply conseq;
         Reconstr.scrush (** hammer *).
         intros. apply H with (s := s) (t := s);
	       Reconstr.htrivial (@H0)
		     (@Big_Step.WhileFalse)
	       Reconstr.Empty (** hammer *).
Admitted.

Lemma hoare_complete: forall c (P Q: assn), hoare_valid P c Q -> hoare P c Q.
Proof. intros. apply helper. 
       intros. unfold hoare_valid in *. 
       apply H with (s := s); easy.
Qed.


