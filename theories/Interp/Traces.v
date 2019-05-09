(** * ITrees as sets of traces *)

(* begin hide *)
From Coq Require Import
     List
     Logic.ProofIrrelevance.

Import ListNotations.

From Paco Require Import
     paco.

From ITree Require Import
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus
     Eq.SimUpToTaus
     Eq.Shallow.

Local Open Scope itree.
(* end hide *)

Inductive trace {E : Type -> Type} {R : Type} : Type :=
| TEnd : trace
| TRet : R -> trace
| TEventEnd : forall {X}, E X -> trace
| TEventResponse : forall {X}, E X -> X -> trace -> trace
.

Inductive is_traceF {E : Type -> Type} {R : Type} :
  itreeF E R (itree E R) -> @trace E R -> Prop :=
| TraceEmpty : forall t, is_traceF t TEnd
| TraceRet : forall r, is_traceF (RetF r) (TRet r)
| TraceTau : forall t tr,
    is_traceF (observe t) tr ->
    is_traceF (TauF t) tr
| TraceVisEnd : forall X (e : E X) k,
    is_traceF (VisF e k) (TEventEnd e)
| TraceVisContinue : forall X (e : E X) (x : X) k tr,
    is_traceF (observe (k x)) tr ->
    is_traceF (VisF e k) (TEventResponse e x tr)
.

Definition is_trace {E : Type -> Type} {R : Type} (t : itree E R) :=
  is_traceF (observe t).

(* t1 ⊑ t2 *)
Definition trace_incl {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr, is_trace t1 tr -> is_trace t2 tr.

(* t1 ≡ t2 *)
Definition trace_eq {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    trace_incl t1 t2 /\ trace_incl t2 t1.

Lemma is_traceF_tau : forall {E R} (t : itree E R) tr,
    is_traceF (observe t) tr <->
    is_traceF (TauF t) tr.
Proof.
  intros. split; intros.
  - constructor. remember (observe t).
    generalize dependent t.
    induction H; intros; subst; constructor; eapply IHis_traceF; auto.
  - inversion H; subst; try constructor; auto.
Qed.

Lemma sutt_trace_incl : forall {E R} (t1 t2 : itree E R),
    sutt eq t1 t2 -> trace_incl t1 t2.
Proof.
  red. intros. red in H0. remember (observe t1).
  generalize dependent t1. generalize dependent t2.
  induction H0; intros; try solve [constructor].
  - punfold H. rewrite <- Heqi in H.
    remember (RetF _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0; red; rewrite <- Heqi1; constructor.
    eapply IHsuttF; eauto.
  - apply IHis_traceF with (t1:=t); auto.
    apply sutt_inv_tau_left. red. red in H. rewrite <- Heqi in H. auto.
  - punfold H. rewrite <- Heqi in H.
    remember (VisF _ _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0.
    + auto_inj_pair2. subst. red. rewrite <- Heqi1. constructor.
    + red. rewrite <- Heqi1. constructor. eapply IHsuttF; eauto.
  - punfold H. rewrite <- Heqi in H.
    remember (VisF _ _). remember (observe t2).
    generalize dependent t2.
    induction H; intros; try inv Heqi0.
    + pclearbot. auto_inj_pair2. subst. red. rewrite <- Heqi1. constructor.
      eapply IHis_traceF; auto.
    + red. rewrite <- Heqi1. constructor. apply IHsuttF; auto.
Qed.

Lemma eutt_trace_eq : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 -> trace_eq t1 t2.
Proof.
  split.
  - apply sutt_trace_incl; apply eutt_sutt; auto.
  - symmetry in H. apply sutt_trace_incl; apply eutt_sutt; auto.
Qed.

Lemma trace_incl_sutt : forall {E R} (t1 t2 : itree E R),
    trace_incl t1 t2 -> sutt eq t1 t2.
Proof.
  intros E R. pcofix CIH. pstep. intros t1 t2 Hincl.
  unfold trace_incl in *. unfold is_trace in *.
  destruct (observe t1).
  - assert (H : is_traceF (RetF r0 : itreeF E R (itree E R)) (TRet r0)) by constructor.
    apply Hincl in H. clear Hincl. destruct (observe t2); inv H.
    + constructor. auto.
    + constructor.
      remember (observe t). remember (TRet _).
      generalize dependent t.
      induction H1; intros; try inv Heqt0; auto.
      constructor. eapply IHis_traceF; eauto.
  - constructor. right. apply CIH. intros. apply Hincl. constructor. auto.
  - assert (H: is_traceF (VisF e k) (TEventEnd e)) by constructor.
    apply Hincl in H. destruct (observe t2); inv H.
    + constructor.
      assert (forall tr, is_traceF (VisF e k) tr -> is_traceF (observe t) tr).
      {
        intros. rewrite is_traceF_tau. apply Hincl; auto.
      }
      clear Hincl. rename H into Hincl.
      remember (observe t). remember (TEventEnd _).
      generalize dependent t.
      induction H1; intros; try inv Heqt0; auto.
      * constructor. eapply IHis_traceF; eauto.
        intros. rewrite is_traceF_tau. apply Hincl; auto.
      * auto_inj_pair2. subst. constructor. intro. right. apply CIH. intros.
        assert (is_traceF (VisF e k) (TEventResponse e x tr)) by (constructor; auto).
        apply Hincl in H0. inv H0. auto_inj_pair2. subst. auto.
    + auto_inj_pair2. subst. constructor. intro. right. apply CIH. intros.
      assert (is_traceF (VisF e k) (TEventResponse e x tr)) by (constructor; auto).
      apply Hincl in H0. inv H0. auto_inj_pair2. subst. auto.
Qed.

Theorem trace_incl_iff_sutt : forall {E R} (t1 t2 : itree E R),
    sutt eq t1 t2 <-> trace_incl t1 t2.
Proof.
  split.
  - apply sutt_trace_incl.
  - apply trace_incl_sutt.
Qed.

Lemma trace_eq_eutt : forall {E R} (t1 t2 : itree E R),
    trace_eq t1 t2 -> t1 ≈ t2.
Proof.
  intros E R t1 t2 [? ?]. apply sutt_eutt.
  - apply trace_incl_sutt; auto.
  - apply trace_incl_sutt in H0. clear H.
    generalize dependent t1. generalize dependent t2. pcofix CIH; pstep; intros.
    punfold H0. induction H0; constructor; try red; pclearbot; eauto with paco.
    right. rewrite itree_eta'. eauto with paco.
Qed.

Theorem trace_eq_iff_eutt : forall {E R} (t1 t2 : itree E R),
    t1 ≈ t2 <-> trace_eq t1 t2.
Proof.
  split.
  - apply eutt_trace_eq.
  - apply trace_eq_eutt.
Qed.

Inductive event (E : Type -> Type) : Type :=
| Event : forall {X}, E X -> X -> event E
.

(* [step_ ev t' t] if [t] steps to [t'] (read right to left!)
   with visible event [ev]. *)
Inductive step_ {E : Type -> Type} {R : Type}
          (ev : event E) (t' : itree E R) :
  itree E R -> Prop :=
| StepTau : forall t, step_ ev t' t -> step_ ev t' (Tau t)
| StepVis : forall X (e : E X) (x : X) k,
    ev = Event _ e x ->
    t' = k x ->
    step_ ev t' (Vis e k)
.

Definition step {E : Type -> Type} {R : Type}
           (ev : event E) (t t' : itree E R) : Prop :=
  step_ ev t' t.

CoInductive simulates {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
| SimStep : forall t1 t2,
    (forall ev t1',
        step ev t1 t1' ->
        exists t2', step ev t2 t2' /\ simulates t1' t2') ->
    simulates t1 t2.

Theorem simulates_trace_incl {E : Type -> Type} {R : Type} :
  forall t1 t2 : itree E R,
    simulates t1 t2 -> trace_incl t1 t2.
Proof.
Abort.

(* Set-of-traces monad *)
Definition traces (E : Type -> Type) (R : Type) : Type :=
  @trace E R -> Prop.

(* Append two traces, ignoring the end of the first trace. *)
Fixpoint app_trace {E R S} (tr1 : @trace E R) (tr2 : @trace E S) : @trace E S :=
  match tr1 with
  | TEventResponse e x tr => TEventResponse e x (app_trace tr tr2)
  | _ => tr2
  end.

Fixpoint trace_end {E R} (tr : @trace E R) : trace :=
  match tr with
  | TEventResponse _ _ tr => trace_end tr
  | _ => tr
  end.

Lemma trace_end_app_trace_TEnd : forall {E R1 R2} (tr : @trace E R1),
    trace_end (app_trace tr TEnd : @trace E R2) = TEnd.
Proof.
  intros. induction tr; auto.
Qed.

Lemma app_trace_TRet : forall {E R} (tr : @trace E R) (r : R),
    trace_end tr = (TRet r) ->
    app_trace tr (TRet r) = tr.
Proof.
  intros. induction tr; auto.
  simpl. f_equal. apply IHtr. inv H. auto.
Qed.

(** remove_end **)

Fixpoint remove_end_one {E R} (tr : @trace E R) : @trace E R :=
  match tr with
  | TEventResponse e x TEnd => TEnd
  | TEventResponse e x tr => TEventResponse e x (remove_end_one tr)
  | _ => TEnd
  end.

Fixpoint remove_end {E R} (tr : @trace E R) (n : nat) : trace :=
  match n with
  | 0 => tr
  | S n => remove_end (remove_end_one tr) n
  end.

Lemma remove_end_remove_end_one_commute : forall {E R} (tr : @trace E R) n,
    remove_end (remove_end_one tr) n = remove_end_one (remove_end tr n).
Proof.
  intros. generalize dependent tr.
  induction n; intros; auto. simpl. rewrite <- IHn. auto.
Qed.

Lemma remove_end_Sn : forall {E R} (tr : @trace E R) n,
    remove_end tr (S n) = remove_end (remove_end tr n) 1.
Proof.
  intros. simpl. rewrite remove_end_remove_end_one_commute. auto.
Qed.

Lemma trace_end_remove_end_one : forall {E R} (tr : @trace E R),
    trace_end (remove_end_one tr) = TEnd.
Proof.
  intros. induction tr; simpl; auto.
  destruct tr; auto.
Qed.

(* Lemma trace_end_remove_end : forall {E R} (tr : @trace E R) n, *)
(*     trace_end (remove_end tr (S n)) = TEnd. *)
(* Proof. *)
(*   intros. induction n; auto. *)
(*   - apply trace_end_TEnd_remove_end_one. *)
(*   - simpl in *. rewrite remove_end_remove_end_one_commute. *)
(*     apply trace_end_TEnd_remove_end_one. *)
(* Qed. *)

Lemma remove_end_one_app_trace_commute :
  forall {E R1 R2} X (tr1 : @trace E R1) (tr2 : @trace E R2) (e : E X) (x : X),
  remove_end_one (app_trace tr1 (TEventResponse e x tr2)) =
  app_trace tr1 (remove_end_one (TEventResponse e x tr2)).
Proof.
  intros. induction tr1; auto.
  simpl. rewrite IHtr1. destruct tr1; auto.
Qed.

Lemma app_trace_TEnd : forall {E R} (tr : @trace E R),
    app_trace tr TEnd = tr \/
    app_trace tr TEnd = remove_end_one tr.
Proof.
  intros. induction tr; auto.
  destruct IHtr.
  - left. simpl. rewrite H. auto.
  - simpl. rewrite H. destruct tr; auto.
Qed.

(** trace_len **)

Fixpoint trace_len {E R} (tr : @trace E R) : nat :=
  match tr with
  | TEnd => 0
  | TRet _ => 1
  | TEventEnd _ => 1
  | TEventResponse _ _ tr => 1 + trace_len tr
  end.

Lemma trace_len_remove_end_one : forall {E R} (tr : @trace E R) X e (x : X),
    trace_len tr = trace_len (remove_end_one (TEventResponse e x tr)).
Proof.
  intros. induction tr; auto.
  simpl. f_equal. destruct tr; auto.
Qed.

(** prefix_closed **)

Definition prefix_closed {E R} (ts : traces E R) :=
  forall tr n, ts tr -> ts (remove_end tr n).

(* Helper lemma *)
Lemma is_trace_remove_one : forall {E R} (t : itree E R) tr,
    is_trace t tr ->
    is_trace t (remove_end_one tr).
Proof.
  intros. red in H. red.
  induction H; simpl in *; try constructor; auto.
  destruct tr; constructor; auto.
Qed.
Lemma is_trace_prefix_closed : forall {E R} (t : itree E R),
    prefix_closed (is_trace t).
Proof.
  unfold prefix_closed. intros. generalize dependent tr. generalize dependent t.
  induction n; intros; auto; simpl.
  apply is_trace_remove_one in H. auto.
Qed.

Lemma prefix_closed_TEnd : forall {E R} (ts : traces E R),
    (exists tr, ts tr) ->
    prefix_closed ts ->
    ts TEnd.
Proof.
  intros. destruct H as [tr ?]. red in H0.
  remember (trace_len tr).
  generalize dependent tr.
  induction n; intros.
  - destruct tr; inv Heqn. auto.
  - destruct tr; inv Heqn; auto.
    + specialize (H0 (TRet r) 1). auto.
    + specialize (H0 (TEventEnd e) 1). auto.
    + specialize (H0 _ 1 H). apply (IHn _ H0). apply trace_len_remove_end_one.
Qed.

(** casting functions **)

Fixpoint cast_TEnd {E R1 R2} (tr : @trace E R1) (H : trace_end tr = TEnd) : @trace E R2.
  induction tr.
  - apply TEnd.
  - discriminate H.
  - discriminate H.
  - specialize (IHtr H). apply (TEventResponse e x IHtr).
Defined.

Fixpoint cast_TEventEnd {E R1 R2} X (e : E X)
         (tr : @trace E R1) (H : trace_end tr = TEventEnd e) : @trace E R2.
  induction tr.
  - discriminate H.
  - discriminate H.
  - apply (TEventEnd e).
  - specialize (IHtr H). apply (TEventResponse e0 x IHtr).
Defined.

(** lemmas about the casting function **)

(* The types R are the same, but this shows that the function does not change the trace *)
Lemma cast_TEnd_same : forall {E R} (tr : @trace E R) H, cast_TEnd tr H = tr.
Proof.
  intros. induction tr; try inv H; auto.
  simpl in *. f_equal. specialize (IHtr H). rewrite <- IHtr.
  unfold cast_TEnd. simpl. destruct tr; auto.
Qed.
Lemma cast_TEventEnd_same : forall {E R} X
                              (tr : @trace E R)
                              (e : E X)
                              (H : trace_end tr = TEventEnd e),
    cast_TEventEnd X e tr H = tr.
Proof.
  intros. induction tr; try inv H; auto.
  simpl in *. f_equal. specialize (IHtr H). rewrite <- IHtr.
  unfold cast_TEnd. simpl. destruct tr; auto.
Qed.

Lemma trace_eq_cast_TEnd_eq : forall {E R1 R2} (tr tr' : @trace E R1) H H',
    tr = tr' ->
    (cast_TEnd tr H : @trace E R2) = cast_TEnd tr' H'.
Proof.
  intros. subst. f_equal. apply proof_irrelevance.
Qed.
Lemma trace_eq_cast_TEventEnd_eq : forall {E R1 R2} X (tr tr' : @trace E R1) (e : E X) H H',
    tr = tr' ->
    (cast_TEventEnd X e tr H : @trace E R2) = cast_TEventEnd X e tr' H'.
Proof.
  intros. subst. f_equal. apply proof_irrelevance.
Qed.

(* commuting also works under cast *)
Lemma cast_TEnd_remove_end_remove_end_one_commute : forall {E R1 R2} (tr : @trace E R1) n H H',
    cast_TEnd (remove_end (remove_end_one tr) n) H =
    (cast_TEnd (remove_end_one (remove_end tr n)) H' : @trace E R2).
Proof.
  intros. apply trace_eq_cast_TEnd_eq. rewrite remove_end_remove_end_one_commute. auto.
Qed.
Lemma cast_TEventEnd_remove_end_remove_end_one_commute :
  forall {E R1 R2} X (tr : @trace E R1) (e : E X) n H H',
    cast_TEventEnd X e (remove_end (remove_end_one tr) n) H =
    (cast_TEventEnd X e (remove_end_one (remove_end tr n)) H' : @trace E R2).
Proof.
  intros. apply trace_eq_cast_TEventEnd_eq. rewrite remove_end_remove_end_one_commute. auto.
Qed.

(* move the cast inside a trace *)
Lemma cast_TEnd_unfold : forall {E R1 R2 X} (e : E X) (x : X) (tr : @trace E R1) H H',
    cast_TEnd (TEventResponse e x tr) H = TEventResponse e x (cast_TEnd tr H' : @trace E R2).
Proof.
  intros. destruct tr; auto; try solve [inv H'].
  simpl in *. repeat f_equal. apply proof_irrelevance.
Qed.
Lemma cast_TEventEnd_unfold :
  forall {E R1 R2} X X' (e : E X) (e' : E X') (x : X') (tr : @trace E R1) H H',
    cast_TEventEnd X e (TEventResponse e' x tr) H =
    TEventResponse e' x (cast_TEventEnd X e tr H' : @trace E R2).
Proof.
  intros. destruct tr; auto; try solve [inv H'].
  simpl in *. repeat f_equal. apply proof_irrelevance.
Qed.

Opaque cast_TEnd.
Opaque cast_TEventEnd.

Lemma cast_TEnd_TEnd : forall {E R1 R2} (tr : @trace E R1) H,
    (cast_TEnd tr H : @trace E R2) = TEnd <->
    tr = TEnd.
Proof.
  split; intros; destruct tr; auto; inv H0.
Qed.
Lemma cast_TEventEnd_TEventEnd : forall {E R1 R2} (tr : @trace E R1) X (e : E X) H,
    (cast_TEventEnd X e tr H : @trace E R2) = TEventEnd e <->
    tr = TEventEnd e.
Proof.
  split; intros; destruct tr; auto; inv H0.
Qed.

Lemma cast_TEnd_trace_end : forall {E R1 R2} (tr : @trace E R1) H,
    trace_end (cast_TEnd tr H) = (TEnd : @trace E R2).
Proof.
  intros. induction tr; auto; try solve [inv H]. simpl in H.
  rewrite (cast_TEnd_unfold _ _ _ _ H). simpl. apply IHtr; auto.
Qed.

Lemma cast_TEnd_remove_end_one_commute : forall {E R1 R2} (tr : @trace E R1) H H',
    (cast_TEnd (remove_end_one tr) H : @trace E R2) =
    remove_end_one (cast_TEnd tr H').
Proof.
  intros. induction tr; auto; try inv H'.
  erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
  simpl.
  destruct tr; auto; try inv H'.
  erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
  erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
  f_equal.
  erewrite IHtr. Unshelve. 2: { auto. }
  clear IHtr. f_equal.
  erewrite cast_TEnd_unfold. auto.
Qed.

Lemma cast_TEnd_remove_end_commute : forall {E R1 R2} (tr : @trace E R1) n H H',
    (cast_TEnd (remove_end tr n) H : @trace E R2) =
    remove_end (cast_TEnd tr H') n.
Proof.
  intros. generalize dependent tr. induction n; intros; auto.
  - simpl. f_equal. apply proof_irrelevance.
  - simpl. simpl in H. pose proof H. rewrite remove_end_remove_end_one_commute in H0.
    rewrite (cast_TEnd_remove_end_remove_end_one_commute _ _ _ H0).
    erewrite cast_TEnd_remove_end_one_commute.
    rewrite remove_end_remove_end_one_commute. erewrite IHn. auto.
    Unshelve. destruct n; auto. rewrite remove_end_Sn. apply trace_end_remove_end_one.
Qed.

Lemma cast_TEventEnd_trace_end : forall {E R1 R2} (tr : @trace E R1) X (e : E X) H,
    trace_end (cast_TEventEnd X e tr H) = (TEventEnd e : @trace E R2).
Proof.
  intros. induction tr; auto; try solve [inv H]. simpl in H.
  rewrite (cast_TEventEnd_unfold _ _ _ _ _ _ _ H). simpl. apply IHtr; auto.
Qed.

Lemma cast_TEventEnd_remove_end_one_commute' : forall {E R1 R2} X e (tr : @trace E R1) H H',
    (cast_TEnd (remove_end_one tr) H : @trace E R2) =
    remove_end_one (cast_TEventEnd X e tr H').
Proof.
  intros. induction tr; auto; try inv H'.
  erewrite cast_TEventEnd_unfold. Unshelve. 2: { auto. }
  simpl. destruct tr; auto; try inv H'.
  erewrite cast_TEventEnd_unfold. Unshelve. 2: { auto. }
  erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
  f_equal.
  erewrite IHtr. Unshelve. 2: { auto. }
  clear IHtr. f_equal.
  erewrite cast_TEventEnd_unfold. auto.
Qed.

Lemma cast_TEventEnd_remove_end_commute' : forall {E R1 R2} X e (tr : @trace E R1) n H H',
    (cast_TEnd (remove_end tr n) H : @trace E R2) =
    remove_end (cast_TEventEnd X e tr H') n.
Proof.
  intros. generalize dependent tr. induction n; intros; auto.
  - simpl in *. pose proof H. pose proof H'. rewrite H0 in H1. inv H1.
  - simpl. simpl in H. pose proof H. rewrite remove_end_remove_end_one_commute in H0.
    rewrite (cast_TEnd_remove_end_remove_end_one_commute _ _ _ H0).
    destruct n.
    + simpl in *. clear IHn. clear H. apply cast_TEventEnd_remove_end_one_commute'.
    + erewrite cast_TEnd_remove_end_one_commute.
      Unshelve. 2: { rewrite remove_end_Sn. apply trace_end_remove_end_one. }
      rewrite remove_end_remove_end_one_commute. erewrite IHn. auto.
Qed.

(** TODO *)
Lemma app_trace_TEnd' : forall {E R1 R2} (tr : @trace E R1) H,
    app_trace tr TEnd = (cast_TEnd tr H : @trace E R2) \/
    app_trace tr TEnd = remove_end_one (cast_TEnd tr H : @trace E R2).
Proof.
  intros. induction tr; auto; try inv H. simpl in H.
  destruct (IHtr H).
  - left. simpl. rewrite H0. erewrite cast_TEnd_unfold; auto.
  - simpl. rewrite H0. destruct tr; auto; inv H.
Qed.
Lemma app_trace_TEnd'' : forall {E R1 R2} (tr : @trace E R1) H,
    cast_TEnd (app_trace tr TEnd : @trace E R2) H = tr \/
    cast_TEnd (app_trace tr TEnd) H = remove_end_one tr.
Proof.
  intros. induction tr; auto; try inv H. simpl in H.
  edestruct IHtr. Unshelve. 3: auto.
  - left. simpl. erewrite cast_TEnd_unfold. rewrite H0. auto.
  - simpl. erewrite cast_TEnd_unfold. rewrite H0. destruct tr; auto; inv H.
Qed.

(* Lemma remove_end_one_app_trace_TRet : forall {E R} (tr : @trace E R) (r : R), *)
(*     remove_end_one (app_trace tr (TRet r)) = tr \/ *)
(*     remove_end_one (app_trace tr (TRet r)) = remove_end_one tr. *)
(* Proof. *)
(*   intros. induction tr; auto. *)
(*   destruct IHtr; simpl; rewrite H; destruct tr; auto. *)
(* Qed. *)

Lemma cast_TEnd_remove_end_one_app_trace_TRet : forall {E R1 R2} (tr : @trace E R1) (r : R2) H,
    cast_TEnd (remove_end_one (app_trace tr (TRet r))) H = tr \/
    cast_TEnd (remove_end_one (app_trace tr (TRet r))) H = remove_end_one tr.
Proof.
  intros. induction tr; auto.
  edestruct IHtr; clear IHtr; simpl. Unshelve. 3: { apply trace_end_remove_end_one. }
  - left. destruct tr; simpl in *; auto.
    + erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
      rewrite <- H0. auto.
    + inv H0.
    + erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
      rewrite <- H0. repeat f_equal. apply proof_irrelevance.
  - destruct tr; simpl in *; auto.
    right. rewrite <- H0. erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
    repeat f_equal. apply proof_irrelevance.
Qed.

Lemma cast_TEnd_remove_end_one_app_trace_TEventEnd :
  forall {E R1 R2} X (tr : @trace E R1) (e : E X) H,
    cast_TEnd (remove_end_one (app_trace tr (TEventEnd e : @trace E R2))) H = tr \/
    cast_TEnd (remove_end_one (app_trace tr (TEventEnd e))) H = remove_end_one tr.
Proof.
  intros. induction tr; auto.
  edestruct IHtr; clear IHtr. Unshelve. 3: { apply trace_end_remove_end_one. }
  - left. destruct tr; simpl in *; auto.
    + erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
      rewrite <- H0. auto.
    + inv H0.
    + erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
      rewrite <- H0. repeat f_equal. apply proof_irrelevance.
  - destruct tr; simpl in *; auto.
    right. rewrite <- H0. erewrite cast_TEnd_unfold. Unshelve. 2: { auto. }
    repeat f_equal. apply proof_irrelevance.
Qed.

(* TODO look at app_trace discarding empty end cases *)
Definition bind_traces {E : Type -> Type} {R1 R2 : Type}
           (ts : traces E R1) (kts : R1 -> traces E R2) : traces E R2 :=
  fun tr =>
    (exists (H : trace_end tr = TEnd), ts (cast_TEnd _ H)) \/
    (exists X (e : E X) (H : trace_end tr = TEventEnd e), ts (cast_TEventEnd _ _ _ H)) \/
    (exists r tr1 tr2,
        tr = app_trace tr1 tr2 /\
        trace_end tr1 = TRet r /\
        ts tr1 /\
        kts r tr2).
Lemma bind_prefix_closed : forall E R1 R2 (ts : traces E R1) (kts : R1 -> traces E R2),
    prefix_closed ts ->
    (forall (r : R1), prefix_closed (kts r)) ->
    prefix_closed (bind_traces ts kts).
Proof.
  red. intros.
  induction n; auto. red in H1.
  destruct H1 as [[? ?] | [[X [e ?]] | [r [tr1 [tr2 [? [? [? ?]]]]]]]].
  - red. left. red in H.
    eexists. erewrite cast_TEnd_remove_end_commute.
    apply H; eauto.
    Unshelve. rewrite remove_end_Sn. apply trace_end_remove_end_one.
  - left. eexists. Unshelve. 2: { rewrite remove_end_Sn. apply trace_end_remove_end_one. }
    destruct H1.
    rewrite (cast_TEventEnd_remove_end_commute' X e _ _ _ x).
    apply H. auto.
  - subst. red in IHn.
    destruct IHn as [[? ?] | [[X [e [? ?]]] | [r' [tr1' [tr2' [? [? [? ?]]]]]]]].
    + left. eexists. Unshelve. 2: { rewrite remove_end_Sn. apply trace_end_remove_end_one. }
      simpl. erewrite cast_TEnd_remove_end_remove_end_one_commute.
      Unshelve. 2: { apply trace_end_remove_end_one. }
      erewrite cast_TEnd_remove_end_one_commute. Unshelve. 2: { auto. }
      red in H. apply (H _ 1). auto.
    + left. eexists. Unshelve. 2: { rewrite remove_end_Sn. apply trace_end_remove_end_one. }
      simpl. erewrite cast_TEnd_remove_end_remove_end_one_commute.
      Unshelve. 2: { apply trace_end_remove_end_one. }
      erewrite cast_TEventEnd_remove_end_one_commute'. Unshelve. all: auto.
      red in H. apply (H _ 1). auto.
    + simpl. rewrite remove_end_remove_end_one_commute.
      rewrite H1. clear H1.
      induction tr2'; simpl in *.
      * left. eexists. Unshelve. 2: { apply trace_end_remove_end_one; auto. }
        erewrite cast_TEnd_remove_end_one_commute.
        Unshelve. 2: { apply trace_end_app_trace_TEnd. }
        apply (H _ 1). edestruct (@app_trace_TEnd'' E R1 R2 tr1'); rewrite H1; auto.
        apply (H _ 1). auto.
      * left. eexists. Unshelve. 2: { apply trace_end_remove_end_one; auto. }
        edestruct (@cast_TEnd_remove_end_one_app_trace_TRet E R1 R2); rewrite H1; auto.
        apply (H _ 1). auto.
      * left. eexists. Unshelve. 2: { apply trace_end_remove_end_one; auto. }
        edestruct (@cast_TEnd_remove_end_one_app_trace_TEventEnd E R1 R2); rewrite H1; auto.
        apply (H _ 1). auto.
      * right. right. exists r', tr1', (remove_end_one (TEventResponse e x tr2')).
        repeat split; auto. apply remove_end_one_app_trace_commute.
        specialize (H0 _ _ 1 H7). auto.
Qed.

Definition ret_traces {E : Type -> Type} {R : Type}
           (r : R) : traces E R :=
  fun tr =>
    tr = TEnd \/
    tr = TRet r.
Lemma ret_prefix_closed : forall E R (r : R), prefix_closed (ret_traces r : traces E R).
Proof.
  red. intros.
  induction n; simpl; auto.
  inv H; simpl; auto.
  clear IHn. induction n; simpl; auto. constructor. auto.
Qed.

Lemma left : forall E R1 R2 (r : R1) (f : R1 -> traces E R2) (t : trace),
    (forall r', prefix_closed (f r')) ->
    (forall r', f r' TEnd) ->
    bind_traces (ret_traces r) f t <-> f r t.
Proof.
  split.
  {
    intros. red in H1.
    destruct H1 as [[? ?] | [? | [? [? [? [? [? [? ?]]]]]]]]; subst.
    - inv H1.
      + rewrite cast_TEnd_TEnd in H2. subst. auto.
      + pose proof (@cast_TEnd_trace_end _ _ R1 t x). rewrite H2 in H1.
        inv H1.
    - destruct H1 as [? [? [? ?]]].
      inv H1; pose proof (@cast_TEventEnd_trace_end _ _ R1 t _ _ x1); rewrite H2 in H1; inv H1.
    - inv H3; inv H2. auto.
  }
  {
    intros. red.
    right. right. exists r. exists (TRet r). exists t. repeat split; auto. right. auto.
  }
Qed.

(* note only 1 R *)
Lemma right : forall E R (ts : traces E R) (t : trace),
    prefix_closed ts ->
    bind_traces ts ret_traces t <-> ts t.
Proof.
  split.
  {
    intros. red in H0.
    destruct H0 as [[] | [[X [e [? ?]]] | [r [tr1 [tr2 [? [? [? ?]]]]]]]]; subst; auto.
    - rewrite cast_TEnd_same in H0. auto.
    - rewrite cast_TEventEnd_same in H0. auto.
    - inv H3.
      + destruct tr1; simpl; try solve [apply prefix_closed_TEnd; eauto].
        destruct (app_trace_TEnd _ e x tr1); simpl in *; rewrite H0; auto.
        apply (H _ 1 H2).
      + rewrite app_trace_TRet; auto.
  }
  {
    intros. red. remember (trace_len t). generalize dependent t.
    induction n; intros; destruct t; inv Heqn.
    - left. exists eq_refl. auto.
    - right. right. exists r. exists (TRet r). exists (TRet r). repeat split; auto. right. auto.
    - right. left. exists X, e, eq_refl. auto.
    - right. right. (* need lemma for cases of traces : different endings *) admit.
  }
Abort.

Lemma assoc : forall E R1 R2 R3 (ts : traces E R1) (f : R1 -> traces E R2) (g : R2 -> traces E R3) t,
    bind_traces (bind_traces ts f) g t <-> bind_traces ts (fun x => bind_traces (f x) g) t.
Proof.
  split; intros.
  {
    red in H. destruct H as [? | [? | ?]].
    - left. destruct H. exists x. destruct H.
      + destruct H. admit.
      + admit.
    - right. left. admit.
    - right. right. admit.
  }
  {
    red in H. destruct H as [? | [? | ?]].
    - left. admit.
  }
Qed.
