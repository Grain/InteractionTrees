(** * ITrees as sets of traces *)

(* begin hide *)
From Coq Require Import
     List.

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

(* (* Get the value in the TRet at the end of the trace, if it exists. *) *)
(* Fixpoint trace_ret {E R} (tr : @trace E R) : option R := *)
(*   match tr with *)
(*   | TRet r => (Some r) *)
(*   | TEventResponse _ _ tr => trace_ret tr *)
(*   | _ => None *)
(*   end. *)

(* Inductive prefix {E : Type -> Type} {R : Type} : @trace E R -> @trace E R -> Prop := *)
(* | PrefixTEnd : forall t, prefix TEnd t *)
(* | PrefixTRet : forall r t, *)
(*     trace_end t = TRet r -> *)
(*     prefix (TRet r) t *)
(* | PrefixTEventEnd : forall X (e : E X) t, *)
(*     trace_end t = TEventEnd e -> *)
(*     prefix (TEventEnd e) t *)
(* | PrefixTEventResponse: forall X (e : E X) (x : X) t1 t2, *)
(*     prefix t1 t2 -> *)
(*     prefix (TEventResponse e x t1) (TEventResponse e x t2) *)
(* . *)

(* Fixpoint remove_end_one {E R} (tr : @trace E R) : trace := *)
(*   match tr with *)
(*   | TEventResponse e x TEnd => TEnd *)
(*   | TEventResponse e x (TRet r) => TRet r *)
(*   | TEventResponse e x (TEventEnd e') => TEventEnd e' *)
(*   | TEventResponse e x tr => TEventResponse e x (remove_end_one tr) *)
(*   | _ => tr *)
(*   end. *)
Fixpoint remove_end_one {E R} (tr : @trace E R) : @trace E R :=
  match tr with
  | TEventResponse e x TEnd => TEnd
  (* | TEventResponse e x (TRet r) => TEnd *)
  (* | TEventResponse e x (TEventEnd e') => TEnd *)
  | TEventResponse e x tr => TEventResponse e x (remove_end_one tr)
  | _ => TEnd
  end.

Fixpoint remove_end {E R} (tr : @trace E R) (n : nat) : trace :=
  match n with
  | 0 => tr
  | S n => remove_end (remove_end_one tr) n
  end.

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

Definition prefix_closed {E R} (ts : traces E R) :=
  forall tr n, ts tr -> ts (remove_end tr n).

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

Fixpoint trace_len {E R} (tr : @trace E R) : nat :=
  match tr with
  | TEnd => 0
  | TRet _ => 1
  | TEventEnd _ => 1
  | TEventResponse _ _ tr => 1 + trace_len tr
  end.

Lemma trace_len_remove_end_one : forall {E R} (tr : @trace E R) X e (x : X),
    trace_len tr = trace_len (remove_end (TEventResponse e x tr) 1).
Proof.
  intros. induction tr; auto.
  simpl. f_equal. destruct tr; auto.
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

(* TODO: Prefix closed property *)
(* is_trace t has these properties and ret/bind preserve these *)

Definition bind_traces {E : Type -> Type} {R S : Type}
           (ts : traces E R) (kts : R -> traces E S) : traces E S :=
  fun tr =>
    (tr = TEnd /\ (* but TEnd should always be in ts? Maybe not if we don't have the condition here? *) ts TEnd) \/
    (* (exists X (e : E X), tr = TEventEnd e /\ ts (TEventEnd e)) \/ *)
    (* (exists X (e : E X), trace_end tr = TEventEnd e /\ ts tr) \/ *)
    (exists r tr1 tr2,
        tr = app_trace tr1 tr2 /\
        trace_end tr1 = TRet r /\
        ts tr1 /\
        kts r tr2).

Definition ret_traces {E : Type -> Type} {R : Type}
           (r : R) : traces E R :=
  fun tr =>
    tr = TEnd \/
    tr = TRet r.

(* Lemma trace_ind' : forall (E : Type -> Type) (R : Type) (P : trace -> Prop), *)
(*     P TEnd -> *)
(*     (forall r : R, P (TRet r)) -> *)
(*     (forall (X : Type) (e : E X), P (TEventEnd e)) -> *)
(*     (forall (X : Type) (e : E X) (x : X) (t : trace), P (remove_end_one t) -> P t) -> *)
(*     forall t : trace, P t. *)
(* Proof. *)
(*   intros. induction t; auto. *)
(* Admitted. *)

Lemma left : forall E R1 R2 (r : R1) (f : R1 -> traces E R2) (t : trace),
    (forall r', prefix_closed (f r')) ->
    bind_traces (ret_traces r) f t <-> f r t.
Proof.
  split.
  {
    intros. red in H0.
    destruct H0 as [[? ?] | [? [? [? [? [? [? ?]]]]]]]; subst.
    (* destruct H as [[? ?] | [[? [? [? ?]]] | [? [? [? [? [? [? ?]]]]]]]]; subst. *)
    - inv H1.
      + admit. (* just add this as additional assumption *)
      + inv H0.
    (* - inv H0; inv H. *)
    - inv H2; inv H1. auto.
  }
  {
    intros. red.
    remember (trace_len t).
    generalize dependent t.
    induction n; intros.
    - destruct t; inv Heqn.
      left. split; auto. constructor; auto.
    - right. destruct t; inv Heqn.
      + exists r. exists (TRet r). exists (TRet r0). repeat split; auto. right; auto.
      + exists r. exists (TRet r). exists (TEventEnd e). repeat split; auto. right; auto.
      + assert (f r (remove_end (TEventResponse e x t) 1)).
        { apply H; auto. }
        pose proof (trace_len_remove_end_one t X e x).
        specialize (IHn _ H1 H2). destruct IHn.
        * destruct H3. inv H3. inv H2. destruct t; inv H6.
          exists r. exists (TRet r). exists (TEventResponse e x TEnd). repeat split; auto.
          right. auto.
        * destruct H3 as [r0 [tr1 [tr2 [? [? [? ?]]]]]].
          exists r0. exists tr1. eexists. repeat split; auto.
          (* oh no *)

  (*       simpl in IHn. specialize (IHn eq_refl). destruct IHn. *)
  (*       * destruct H2. subst. exists *)


  (*   induction t. *)
  (*   - left. split; auto. red. auto. *)
  (*   - right. exists r, (TRet r), (TRet r0). repeat split; auto. right. auto. *)
  (*   - right. exists r, (TRet r), (TEventEnd e). repeat split; auto. right. auto. *)
  (*   - right. assert (f r (remove_end_one t)) by admit. specialize (IHt H0). clear H0. *)
  (*     destruct IHt. *)
  (*     + destruct H0. subst. (* exists r, (TRet r), (TEventResponse e x TEnd). repeat split; auto. *) *)
  (*       admit. *)
  (*     (* + destruct H0 as [? [? [? ?]]]. inv H1; inv H2. *) *)
  (*     + destruct H0 as [? [? [? [? [? [? ?]]]]]]. *)
  (*       exists x0, (TEventResponse e x x1), x2. repeat split; auto. *)
  (*       * rewrite H0. reflexivity. *)
  (*       * admit. *)
  (* } *)
Abort.

Lemma right : forall E R (ts : traces E R) (t : trace),
    bind_traces ts ret_traces t <-> ts t.
Proof.
  split.
  {
    intros. red in H. destruct H as [? | [? | ?]].
    - destruct H. subst. auto.
    - destruct H as [? [? [? ?]]]. subst. auto.
    - destruct H as [? [? [? [? [? [? ?]]]]]]. subst.
  }
Abort.

Lemma assoc : forall E R1 R2 R3 (ts : traces E R1) (f : R1 -> traces E R2) (g : R2 -> traces E R3) t,
    bind_traces (bind_traces ts f) g t <-> bind_traces ts (fun x => bind_traces (f x) g) t.
Proof.
  split.
  {
    intros.
  }
  {

  }
Qed.
