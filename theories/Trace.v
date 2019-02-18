From Coq Require Import
     List
     ProofIrrelevance
     Classes.RelationClasses.

Import ListNotations.

From ITree Require Import
     Core
     Eq.UpToTaus.

From Paco Require Import
     paco.

Inductive event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E
(* An effect without any response from the context (e.g. if X is uninhabited) *)
| EventOut : forall X, E X -> event E
.

Arguments Event {E X}.
Arguments EventOut {E X}.

Definition trace (E : Type -> Type) : Type := list (event E).

Inductive is_traceF {E : Type -> Type} {R : Type} :
  itreeF E R (itree E R) -> trace E -> option R -> Prop :=
| TraceEmpty : forall t, is_traceF t [] None
| TraceRet : forall r,
    is_traceF (RetF r) [] (Some r)
| TraceTau : forall t tr r_,
    is_traceF (observe t) tr r_ ->
    is_traceF (TauF t) tr r_
| TraceVisEvent : forall X (e : E X) (x : X) k tr r_,
    is_traceF (observe (k x)) tr r_ ->
    is_traceF (VisF e k) (Event e x :: tr) r_
| TraceVisEventOut : forall X (e : E X) k,
    is_traceF (VisF e k) [EventOut e] None
.

Definition is_trace {E R} (t : itree E R) := is_traceF (observe t).

Inductive trace' {E : Type -> Type} {R : Type} : Type :=
| TEnd : trace'
| TRet : R -> trace'
| TEventEnd : forall {X}, E X -> trace'
| TEventResponse : forall {X}, E X -> X -> trace' -> trace'
.

Inductive is_traceF' {E R} :
  itreeF E R (itree E R) -> @trace' E R -> Prop :=
| TraceEmpty' : forall t, is_traceF' t TEnd
| TraceRet' : forall r, is_traceF' (RetF r) (TRet r)
| TraceTau' : forall t tr,
    is_traceF' (observe t) tr ->
    is_traceF' (TauF t) tr
| TraceVisEnd' : forall X (e : E X) k,
    is_traceF' (VisF e k) (TEventEnd e)
| TraceVisContinue' : forall X (e : E X) (x : X) k tr,
    is_traceF' (observe (k x)) tr ->
    is_traceF' (VisF e k) (TEventResponse e x tr)
.

Definition is_trace' {E R} (t : itree E R) := is_traceF' (observe t).

(* t1 ⊑ t2 *)
Definition trace_incl {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr r_, is_trace t1 tr r_ -> is_trace t2 tr r_.

Global Instance Reflexive_trace_incl {E R} : Reflexive (@trace_incl E R).
Proof.
  do 3 red. intros. red in H.
  remember tr as tr'. remember r_ as r'. remember (observe x).
  induction H; intros; subst; constructor; auto.
Qed.

Global Instance Transitive_trace_incl {E R} : Transitive (@trace_incl E R).
Proof.
  do 2 red. intros. apply H in H1. apply H0 in H1. assumption.
Qed.

(* t1 ≡ t2 *)
Definition trace_eq {E : Type -> Type} {R : Type} : itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    trace_incl t1 t2 /\ trace_incl t2 t1.

Ltac invert_existTs :=
  repeat match goal with
         | [ H : existT ?P ?p _ = existT ?P ?p _ |- _ ] => apply inj_pair2 in H
         end; subst.

(* A trace is still valid after removing taus *)
Lemma is_traceF_unalltaus_remove: forall {E R} (t1 t2 : itreeF E R (itree E R)) tr r,
    unalltausF t1 t2 ->
    is_traceF t1 tr r ->
    is_traceF t2 tr r.
Proof.
  intros. inv H. induction H1; subst; auto.
  apply IHuntausF; auto. inversion H0; subst; auto; constructor.
Qed.
Lemma is_trace_unalltaus_remove: forall {E R} (t1 t2 : itree E R) tr r,
    unalltausF (observe t1) (observe t2) ->
    is_trace t1 tr r ->
    is_trace t2 tr r.
Proof. intros. eapply is_traceF_unalltaus_remove; eauto. Qed.

(* A trace is still valid after adding taus *)
Lemma is_traceF_unalltaus_add: forall {E R} (t1 t2 : itreeF E R (itree E R)) tr r,
    unalltausF t1 t2 ->
    is_traceF t2 tr r ->
    is_traceF t1 tr r.
Proof.
  intros. inv H.
  induction H1; auto.
  rewrite <- OBS. constructor. auto.
Qed.
Lemma is_trace_unalltaus_add: forall {E R} (t1 t2 : itree E R) tr r,
    unalltausF (observe t1) (observe t2) ->
    is_trace t2 tr r ->
    is_trace t1 tr r.
Proof. intros. eapply is_traceF_unalltaus_add; eauto. Qed.

Lemma eutt_trace_incl : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 -> trace_incl t1 t2.
Proof.
  red. intros. red in H0. remember (observe t1).
  generalize dependent t1. generalize dependent t2.
  induction H0; intros; try solve [constructor].
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (RetF r)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H0). inv EQV. red.
    eapply is_trace_unalltaus_add.
    + simpobs. auto.
    + red. rewrite <- Heqi. constructor.
  - apply IHis_traceF with (t1:=t); auto.
    rewrite <- H. symmetry. apply tauF_eutt. assumption.
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (VisF e k)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H1). inv EQV.
    invert_existTs. inv H1. specialize (H6 x).

    red. remember (VisF _ _) in H2. remember (observe t2).
    generalize dependent t2.
    induction H2; intros; subst.
    + constructor. apply IHis_traceF with (t1:=k x); auto.
      pfold. inversion H6.
      pinversion H1. inversion H1.
    + constructor. eapply IHuntausF; auto.
      * rewrite FIN. apply finite_taus_tau; auto.
      * eapply euttF_tau_right; eauto.
  - pinversion H.
    assert (Hunall: unalltausF (observe t1) (VisF e k)).
    {
      rewrite Heqi. constructor; auto. red. rewrite <- Heqi. auto.
    }
    assert (FIN2: finite_tausF (observe t1)) by (eexists; apply Hunall).
    rewrite FIN in FIN2. inv FIN2.
    specialize (EQV _ _ Hunall H0). inv EQV.
    invert_existTs. inv H0.

    red. remember (VisF _ _) in H1. remember (observe t2).
    generalize dependent t2.
    induction H1; intros; subst; constructor.
    eapply IHuntausF; auto.
    + rewrite FIN. apply finite_taus_tau; auto.
    + eapply euttF_tau_right; eauto.
Qed.

Lemma eutt_trace_eq : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 -> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_incl; auto.
  - symmetry in H. apply eutt_trace_incl; auto.
Qed.

Lemma is_trace_tau : forall {E R} (t : itree E R) tr r,
    is_trace t tr r <->
    is_trace (Tau t) tr r.
Proof.
  intros. split; intros.
  - constructor. unfold is_trace in *. remember (observe t).
    generalize dependent t.
    induction H; intros; subst; constructor; eapply IHis_traceF; auto.
  - inversion H; subst; try constructor; auto.
Qed.

Lemma trace_incl_finite_taus : forall {E R} (t1 t2 : itree E R),
    trace_incl t1 t2 ->
    finite_tausF (observe t1) -> finite_tausF (observe t2).
Proof.
  intros. destruct H0. destruct H0. unfold trace_incl in *.
  remember (observe t1).
  generalize dependent t1.
  induction H0; intros; subst.
  - unfold is_trace in *.
    red in H1. destruct (observe t1) eqn:Ht1; try contradiction.
    + assert (is_traceF (RetF r : itreeF E R (itree E R)) [] (Some r)) by constructor.
      specialize (H _ _ H0).
      remember (Some r) as r'.
      induction H; subst; try inv Heqr'.
      * eapply finite_taus_ret; eauto.
      * rewrite finite_taus_tau; auto.
      * eapply finite_taus_vis; eauto.
    + assert (is_traceF (VisF e k) [EventOut e] None) by constructor.
      specialize (H _ _ H0).
      remember [EventOut e] as tr.
      induction H; subst; try inv Heqtr.
      * rewrite finite_taus_tau; auto.
      * eapply finite_taus_vis; eauto.
  - eapply IHuntausF; auto.
    intros. apply H. red. rewrite <- Heqi. apply is_trace_tau; auto.
Qed.

Lemma trace_eq_eutt : forall {E R} (t1 t2 : itree E R),
    trace_eq t1 t2 -> t1 ≈ t2.
Proof.
  intros E R. pcofix CIH. intros t1 t2 Heq. pfold. constructor.
  - destruct Heq. split; intros; eapply trace_incl_finite_taus; eauto.
  - intros. destruct Heq as [H12 H21]. unfold trace_incl in *. unfold is_trace in *.
    assert (Heq' : forall tr r, is_traceF ot1' tr r <-> is_traceF ot2' tr r).
    {
      intros. split; intros.
      - pose proof (is_traceF_unalltaus_add _ _ _ _ UNTAUS1 H).
        eapply is_traceF_unalltaus_remove; eauto.
      - pose proof (is_traceF_unalltaus_add _ _ _ _ UNTAUS2 H).
        eapply is_traceF_unalltaus_remove; eauto.
    }
    destruct ot1', ot2';
      try solve [inv UNTAUS1; inv H0];
      try solve [inv UNTAUS2; inv H0].
    + assert (is_traceF (RetF r0 : itreeF E R (itree E R)) [] (Some r0)) by constructor.
      rewrite Heq' in H. inv H. constructor.
    + assert (is_traceF (RetF r0 : itreeF E R (itree E R)) [] (Some r0)) by constructor.
      rewrite Heq' in H. inv H.
    + assert (is_traceF (VisF e k) [EventOut e] None) by constructor.
      rewrite Heq' in H. inv H.
    + assert (is_traceF (VisF e k) [EventOut e] None) by constructor.
      rewrite Heq' in H. inv H. invert_existTs.

      constructor. intros. right. apply CIH.
      red. split; red; intros.
      * assert (is_traceF (VisF e k) ((Event e x) :: tr) r_) by (constructor; auto).
        rewrite Heq' in H0. inv H0. invert_existTs. auto.
      * assert (is_traceF (VisF e k0) ((Event e x) :: tr) r_) by (constructor; auto).
        rewrite <- Heq' in H0. inv H0. invert_existTs. auto.
Qed.

Theorem trace_eq_iff_eutt : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 <-> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_eq.
  - apply trace_eq_eutt.
Qed.

(* [step_ ev t' t] if [t] steps to [t'] (read right to left!)
   with visible event [ev]. *)
Inductive step_ {E : Type -> Type} {R : Type}
          (ev : event E) (t' : itree E R) :
  itree E R -> Prop :=
| StepTau : forall t, step_ ev t' t -> step_ ev t' (Tau t)
| StepVis : forall X (e : E X) (x : X) k,
    ev = Event e x ->
    t' = k x ->
    step_ ev t' (Vis e k)
.

Definition step {E : Type -> Type} {R : Type}
           (ev : event E) (t t' : itree E R) : Prop :=
  step_ ev t' t.

CoInductive simulates {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
| SimStep : forall t1 t2,
    (forall ev t1', step ev t1 t1' ->
     exists    t2', step ev t2 t2' /\ simulates t1' t2') ->
    simulates t1 t2.

Theorem simulates_trace_incl {E : Type -> Type} {R : Type} :
  forall t1 t2 : itree E R,
    simulates t1 t2 -> trace_incl t1 t2.
Proof.
Abort.

(* Set-of-traces monad *)
Definition traces (E : Type -> Type) (R : Type) : Type :=
  trace E -> option R -> Prop.

Definition bind_traces {E : Type -> Type} {R S : Type}
           (ts : traces E R) (kts : R -> traces E S) : traces E S :=
  fun tr s_ =>
    (s_ = None /\ ts tr None) \/
    (exists r tr1 tr2,
        tr = tr1 ++ tr2 /\
        ts tr1 (Some r) /\
        kts r tr s_).

Definition ret_traces {E : Type -> Type} {R : Type} :
  R -> traces E R :=
  fun r tr r_ =>
    tr = [] /\ (r_ = None \/ r_ = Some r).
