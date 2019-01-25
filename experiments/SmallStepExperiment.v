From ITree Require Import
     ITree
     Trace.

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
| bt_tau  : forall s s' t r, done s = false -> ss s = inl s' -> big_trace s' t r -> big_trace s t r
| bt_vis  : forall s i e k t r,
    done s = false ->
    ss s = inr (existT _ i (e, k)) ->
    forall (x:i), big_trace (k x) t r -> big_trace s ((Event e x)::t) r.

Fixpoint big_trace_approx (n:nat) (s:state) (t:trace E) (os:option state) : Prop :=
  match n with
  | 0 => os = None /\ t = []
  | S m =>
    (done s = true /\ os = Some s /\ t = []) \/
    (done s = false /\ exists s', ss s = inl s' /\ big_trace_approx m s' t os) \/
    (done s = false /\ exists t' i e k, ss s = inr (existT _ i (e, k))
                 (* exists? *)
                 /\ forall (x:i), t = ((Event e x)::t') /\ (big_trace_approx m (k x) t' os))
end.

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
    - rewrite (not_done_big_inl _ _ H H0). constructor. auto.
    - rewrite (not_done_big_inr _ _ _ _ H H0). constructor. auto.
  }
  {
Admitted.

Lemma semantics_coincide : forall s n t os, big_trace_approx n s t os -> is_trace (big s) t os.
Proof.
  intros s n. revert s.
  induction n; intros.
  - red in H. destruct H. subst. constructor.
  - remember (S n) as n'. rewrite Heqn' in H.
    simpl in H. decompose [or] H; clear H.
    + decompose [and] H0; clear H0. subst. rewrite (done_big _ H). constructor.
    + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inl _ _ H H0).
      constructor. auto.
    + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inr _ _ _ _ H H2).
      constructor. auto.
Qed.

Lemma reverse: forall s t os, is_trace (big s) t os ->
                         exists n, big_trace_approx n s t os.
Proof.
Admitted.
