From ITree Require Import
     ITree
     Trace.

From Paco Require Import paco.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Parameter state : Set.
Parameter done : state -> bool.
Parameter E : Type -> Type.

Parameter ss : state -> state + {i:Type & ((E i) * (i -> state))%type}.

CoFixpoint big (s:state) : itree E state :=
  if done s then Ret s else
    match ss s with
    | inl s' => Tau (big s')
    | inr (existT _ i (e, k)) =>
      Vis e (fun x => big (k x))
    end.

(* This doesn't work if the semantics loops because there can a nontrivial trace but these derivations can't find them *)
Inductive big_trace : state -> (trace E) -> option state -> Prop :=
| bt_done : forall s, done s = true -> big_trace s [] (Some s)
| bt_early : forall s, done s = false -> big_trace s [] None
| bt_tau  : forall s s' t r, done s = false -> ss s = inl s' -> big_trace s' t r -> big_trace s t r
| bt_vis  : forall s i e k t r,
    done s = false ->
    ss s = inr (existT _ i (e, k)) ->
    forall (x:i), big_trace (k x) t r -> big_trace s ((Event e x)::t) r.

Fixpoint big_trace_approx (n:nat) (s:state) (t:trace E) (os:option state) : Prop :=
  match n with
  | 0 =>
    (done s = false /\ os = None /\ t = []) \/
    (done s = true /\ os = Some s /\ t = [])
  | S m =>
    (done s = true /\ os = Some s /\ t = []) \/
    (done s = false /\ exists s', ss s = inl s' /\ big_trace_approx m s' t os) \/
    (done s = false /\ exists i e k,
        ss s = inr (existT _ i (e, k)) /\ ((t = [] /\ os = None) \/
                                          (exists x t', t = (Event e x) :: t' /\
                                                   big_trace_approx m (k x) t' os)))
        (* match t with *)
        (* | [] => True (* i uninhabited *) *)
        (* | (Event e' x) :: t' => big_trace_approx m (k x) t' os *)
        (* end) *)
        (* forall (x:i) t', (big_trace_approx m (k x) t' os) -> t = ((Event e x)::t')) *)
  end.

Lemma relate : forall s t os, big_trace s t os -> exists n, big_trace_approx n s t os.
Admitted.
Lemma relate' : forall n s t os, big_trace_approx n s t os -> big_trace s t os.
Admitted.

(* something like (eutt t1 t2) <-> (forall t os, is_trace t1 t os <-> is_trace t2 t os) *)

Lemma done_big : forall s, done s = true -> big s = Ret s.
Proof.
  intros. rewrite (itree_eta (big s)).
  destruct (observe (big s)) eqn:Hs;
           unfold big in Hs; cbn in Hs; rewrite H in Hs; inversion Hs; auto.
Qed.

Lemma not_done_big_inl : forall s s', done s = false -> ss s = inl s' -> big s = Tau (big s').
Proof.
  intros. rewrite (itree_eta (big s)).
  destruct (observe (big s)) eqn:Hs;
    unfold big in Hs; cbn in Hs; rewrite H in Hs; rewrite H0 in Hs; inversion Hs; auto.
Qed.

Lemma not_done_big_inr : forall s i e k,
    done s = false ->
    ss s = inr (existT _ i (e, k)) ->
    big s = Vis e (fun x => big (k x)).
Proof.
  intros. rewrite (itree_eta (big s)).
  destruct (observe (big s)) eqn:Hs;
    unfold big in Hs; cbn in Hs; rewrite H in Hs; rewrite H0 in Hs; try solve [inversion Hs; subst; auto].
  simpl in Hs. fold big in *. rewrite Hs. auto.
Qed.

Lemma test : forall s t os, big_trace s t os <-> is_trace (big s) t os.
Proof.
  intros. split; intros.
  {
    induction H.
    - rewrite (done_big _ H). constructor.
    - constructor.
    - rewrite (not_done_big_inl _ _ H H0). constructor. auto.
    - rewrite (not_done_big_inr _ _ _ _ H H0). constructor. auto.
  }
  {
    remember (big s) as tree.
    induction H.
    -
Admitted.

Lemma semantics_coincide : forall s n t os, big_trace_approx n s t os -> is_trace (big s) t os.
Proof.
  intros s n. revert s.
  induction n; intros.
  - red in H. destruct H.
    + decompose [and] H; subst. constructor.
    + decompose [and] H; subst. rewrite (done_big _ H0). constructor.
  - remember (S n) as n'. rewrite Heqn' in H.
    simpl in H. decompose [or] H; clear H.
    + decompose [and] H0; clear H0. subst. rewrite (done_big _ H). constructor.
    + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inl _ _ H H0).
      constructor. auto.
    + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inr _ _ _ _ H H0).
      destruct H3. subst.  destruct H1. subst. constructor.
      decompose [ex and] H1. subst. constructor. auto.
Qed.

Lemma reverse: forall s t os, is_trace (big s) t os ->
                         exists n, big_trace_approx n s t os.
Proof.
  intros. remember (big s) as tree. induction H.
  - admit.
  -
Admitted.

Lemma is_trace_unalltaus: forall E R (t t' : itree E R) l r n,
    is_trace t l r ->
    unalltaus n t t' ->
    is_trace t' l r.
Proof.
  intros. revert n H0. induction H; intros.
  - constructor.
  - rewrite (itree_eta t') in *. destruct (observe t'); inversion H0; subst; constructor.
  - eapply IHis_trace. apply (unalltaus_tau _ _ _ H0).
  - inversion H0; subst; clear H0. constructor. auto.
Qed.

Lemma is_trace_unalltaus': forall E R (t t' : itree E R) l r n,
    is_trace t' l r ->
    unalltaus n t t' ->
    is_trace t l r.
Proof.
  intros. induction H0; try constructor; auto.
Qed.

Lemma eutt_traces: forall E R (t1 t2 : itree E R),
    eutt t1 t2 <->
    (forall t r, is_trace t1 t r <-> is_trace t2 t r).
Proof.
  intros. split; intros.
  { split; intros.
    - induction H0.
      + constructor.
      + assert (t2 = Ret r) by admit. subst. constructor.
      + apply IHis_trace. admit.
      + assert (t2 = Vis e k) by admit. subst. constructor. assumption.
    - admit.
  }
  { pcofix IH. pfold. constructor; intros.
    - split; intros.
      + red in H0. decompose [ex] H0; clear H0. admit.
      + (* same *) admit.
    - assert (forall t r, is_trace t1' t r <-> is_trace t2' t r).
      { intros. split; intros.
        - pose proof (is_trace_unalltaus' _ _ _ _ _ _ _ H0 UNTAUS1).
          rewrite H in H1. eapply is_trace_unalltaus; eauto.
        - pose proof (is_trace_unalltaus' _ _ _ _ _ _ _ H0 UNTAUS2).
          rewrite <- H in H1. eapply is_trace_unalltaus; eauto.
      }
      (* rewrite (itree_eta t1'). rewrite (itree_eta t2') in *. destruct (observe t1') in *; destruct (observe t2'). *)
      admit.
Admitted.
