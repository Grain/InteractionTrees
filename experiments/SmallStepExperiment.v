From ITree Require Import
     ITree
     Trace.

From Paco Require Import paco.

Require Import ProofIrrelevance.

Require Import List.
Import ListNotations.
Open Scope list_scope.

(* Parameter state : Set. *)
(* Parameter done : state -> bool. *)
(* Parameter E : Type -> Type. *)

(* Parameter ss : state -> state + {i:Type & ((E i) * (i -> state))%type}. *)

(* CoFixpoint big (s:state) : itree E state := *)
(*   if done s then Ret s else *)
(*     match ss s with *)
(*     | inl s' => Tau (big s') *)
(*     | inr (existT _ i (e, k)) => *)
(*       Vis e (fun x => big (k x)) *)
(*     end. *)

(* (* This doesn't work if the semantics loops because there can a nontrivial trace but these derivations can't find them *) *)
(* Inductive big_trace : state -> (trace E) -> option state -> Prop := *)
(* | bt_done : forall s, done s = true -> big_trace s [] (Some s) *)
(* | bt_early : forall s, done s = false -> big_trace s [] None *)
(* | bt_tau  : forall s s' t r, done s = false -> ss s = inl s' -> big_trace s' t r -> big_trace s t r *)
(* | bt_vis  : forall s i e k t r, *)
(*     done s = false -> *)
(*     ss s = inr (existT _ i (e, k)) -> *)
(*     forall (x:i), big_trace (k x) t r -> big_trace s ((Event e x)::t) r. *)

(* Fixpoint big_trace_approx (n:nat) (s:state) (t:trace E) (os:option state) : Prop := *)
(*   match n with *)
(*   | 0 => *)
(*     (done s = false /\ os = None /\ t = []) \/ *)
(*     (done s = true /\ os = Some s /\ t = []) *)
(*   | S m => *)
(*     (done s = true /\ os = Some s /\ t = []) \/ *)
(*     (done s = false /\ exists s', ss s = inl s' /\ big_trace_approx m s' t os) \/ *)
(*     (done s = false /\ exists i e k, *)
(*         ss s = inr (existT _ i (e, k)) /\ ((t = [] /\ os = None) \/ *)
(*                                           (exists x t', t = (Event e x) :: t' /\ *)
(*                                                    big_trace_approx m (k x) t' os))) *)
(*         (* match t with *) *)
(*         (* | [] => True (* i uninhabited *) *) *)
(*         (* | (Event e' x) :: t' => big_trace_approx m (k x) t' os *) *)
(*         (* end) *) *)
(*         (* forall (x:i) t', (big_trace_approx m (k x) t' os) -> t = ((Event e x)::t')) *) *)
(*   end. *)

(* Lemma relate : forall s t os, big_trace s t os -> exists n, big_trace_approx n s t os. *)
(* Admitted. *)
(* Lemma relate' : forall n s t os, big_trace_approx n s t os -> big_trace s t os. *)
(* Admitted. *)

(* (* something like (eutt t1 t2) <-> (forall t os, is_trace t1 t os <-> is_trace t2 t os) *) *)

(* Lemma done_big : forall s, done s = true -> big s = Ret s. *)
(* Proof. *)
(*   intros. rewrite (itree_eta (big s)). *)
(*   destruct (observe (big s)) eqn:Hs; *)
(*            unfold big in Hs; cbn in Hs; rewrite H in Hs; inversion Hs; auto. *)
(* Qed. *)

(* Lemma not_done_big_inl : forall s s', done s = false -> ss s = inl s' -> big s = Tau (big s'). *)
(* Proof. *)
(*   intros. rewrite (itree_eta (big s)). *)
(*   destruct (observe (big s)) eqn:Hs; *)
(*     unfold big in Hs; cbn in Hs; rewrite H in Hs; rewrite H0 in Hs; inversion Hs; auto. *)
(* Qed. *)

(* Lemma not_done_big_inr : forall s i e k, *)
(*     done s = false -> *)
(*     ss s = inr (existT _ i (e, k)) -> *)
(*     big s = Vis e (fun x => big (k x)). *)
(* Proof. *)
(*   intros. rewrite (itree_eta (big s)). *)
(*   destruct (observe (big s)) eqn:Hs; *)
(*     unfold big in Hs; cbn in Hs; rewrite H in Hs; rewrite H0 in Hs; try solve [inversion Hs; subst; auto]. *)
(*   simpl in Hs. fold big in *. rewrite Hs. auto. *)
(* Qed. *)

(* Lemma test : forall s t os, big_trace s t os <-> is_trace (big s) t os. *)
(* Proof. *)
(*   intros. split; intros. *)
(*   { *)
(*     induction H. *)
(*     - rewrite (done_big _ H). constructor. *)
(*     - constructor. *)
(*     - rewrite (not_done_big_inl _ _ H H0). constructor. auto. *)
(*     - rewrite (not_done_big_inr _ _ _ _ H H0). constructor. auto. *)
(*   } *)
(*   { *)
(*     remember (big s) as tree. *)
(*     induction H. *)
(*     - *)
(* Admitted. *)

(* Lemma semantics_coincide : forall s n t os, big_trace_approx n s t os -> is_trace (big s) t os. *)
(* Proof. *)
(*   intros s n. revert s. *)
(*   induction n; intros. *)
(*   - red in H. destruct H. *)
(*     + decompose [and] H; subst. constructor. *)
(*     + decompose [and] H; subst. rewrite (done_big _ H0). constructor. *)
(*   - remember (S n) as n'. rewrite Heqn' in H. *)
(*     simpl in H. decompose [or] H; clear H. *)
(*     + decompose [and] H0; clear H0. subst. rewrite (done_big _ H). constructor. *)
(*     + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inl _ _ H H0). *)
(*       constructor. auto. *)
(*     + decompose [ex and] H1; clear H1. subst. rewrite (not_done_big_inr _ _ _ _ H H0). *)
(*       destruct H3. subst.  destruct H1. subst. constructor. *)
(*       decompose [ex and] H1. subst. constructor. auto. *)
(* Qed. *)

(* Lemma reverse: forall s t os, is_trace (big s) t os -> *)
(*                          exists n, big_trace_approx n s t os. *)
(* Proof. *)
(*   intros. remember (big s) as tree. induction H. *)
(*   - admit. *)
(*   - *)
(* Admitted. *)

Ltac invert_existTs :=
  repeat match goal with
         | [ H : existT ?P ?p _ = existT ?P ?p _ |- _ ] => apply inj_pair2 in H
         end.

Lemma is_trace_unalltaus: forall {E R} (t t' : itree E R) l r n,
    is_trace t l r ->
    unalltaus n t t' ->
    is_trace t' l r.
Proof.
  intros. revert n H0. induction H; intros.
  - constructor.
  - rewrite (itree_eta t') in *. destruct (observe t'); inversion H0; subst; constructor.
  - eapply IHis_trace. apply (unalltaus_tau _ _ _ H0).
  - inversion H0; subst; clear H0. constructor. auto.
  - inversion H0; subst; clear H0. constructor.
Qed.

Lemma is_trace_unalltaus': forall {E R} (t t' : itree E R) l r n,
    is_trace t' l r ->
    unalltaus n t t' ->
    is_trace t l r.
Proof.
  intros. induction H0; try constructor; auto.
Qed.

Lemma euttF_tau_one {E R} r (t1 t2 : itree E R) :
  (euttF r (Tau t1) t2) ->
  euttF r t1 t2.
Proof.
  intros. destruct H. econstructor.
  - rewrite <- finite_taus_tau. eauto.
  - intros. eapply EQV; apply unalltaus_tau; eauto.
Qed.

Lemma euttF_tau_one' {E R} r (t1 t2 : itree E R) :
  (euttF r t1 (Tau t2)) ->
  euttF r t1 t2.
Proof.
  intros. destruct H. econstructor.
  - symmetry. rewrite <- finite_taus_tau. symmetry. eauto.
  - intros. eapply EQV; apply unalltaus_tau; eauto.
Qed.

Lemma eutt_is_trace : forall {E R} (t1 t2 : itree E R) t r,
    t1 ~~ t2 -> is_trace t1 t r -> is_trace t2 t r.
Proof.
  intros. generalize dependent t2.
  induction H0; intros; try solve [constructor].
  + assert (FINt2: finite_taus t2).
    { apply (finite_taus_eutt _ _ H). apply notau_finite_taus; auto. }
    destruct FINt2. destruct H0.

    assert (unalltaus 0 ((Ret r) : itree E R) (Ret r)) by auto.
    pinversion H. specialize (EQV _ x (Ret r) x0 H1 H0). inversion EQV. subst.

    eapply is_trace_unalltaus'.
    apply TraceRet. eapply H0.
  + apply IHis_trace.
    eapply Transitive_eutt. apply Symmetric_eutt. eapply eutt_tau1. assumption.
  + assert (FINt2: finite_taus t2).
    { apply (finite_taus_eutt _ _ H). apply notau_finite_taus; auto. }
    destruct FINt2. destruct H1.

    assert (unalltaus 0 (Vis e k) (Vis e k)) by auto.
    pinversion H. pose proof (EQV _ x0 (Vis e k) x1 H2 H1) as EQV'. inversion EQV'. clear EQV'.

    invert_existTs. subst.

    remember (Vis _ _) in H1.
    induction H1; subst; constructor.
    * specialize (H7 x). inversion H7; auto. inversion H1.
    * apply IHuntaus; auto. constructor.
        - rewrite finite_taus_tau in FIN. auto.
        - intros. eapply EQV; apply unalltaus_tau; eauto.
        - rewrite finite_taus_tau in FIN. auto.
        - intros. eapply EQV; apply unalltaus_tau; eauto.
  + assert (FINt2: finite_taus t2).
    { apply (finite_taus_eutt _ _ H). apply notau_finite_taus; auto. }
    destruct FINt2. destruct H0.

    assert (unalltaus 0 (Vis e k) (Vis e k)) by auto.
    pinversion H. pose proof (EQV _ x (Vis e k) x0 H1 H0) as EQV'. inversion EQV'. clear EQV'.
    invert_existTs; subst.
    remember (Vis _ _) in H0. induction H0; subst; constructor; auto.
    apply IHuntaus; auto.
        - apply euttF_tau_one'. auto.
        - rewrite finite_taus_tau in FIN. auto.
        - intros. eapply EQV; apply unalltaus_tau; eauto.
Qed.

Lemma is_trace_tau_iff: forall {E R} (t1 t2 : itree E R) t r,
    (is_trace (Tau t1) t r <-> is_trace t2 t r) ->
    (is_trace t1 t r <-> is_trace t2 t r).
Proof.
  intros. split; intros.
  - rewrite <- H. apply TraceTau. assumption.
  - rewrite <- H in H0. remember (Tau t1) as t1'.
    induction H0; try constructor; try inversion Heqt1'; subst; auto.
Qed.

Lemma uninhab_k_eutt: forall {E R} (X : Type) (e : E X) (k1 k2 : X -> itree E R),
    (~ inhabited X) ->
    (Vis e k1) ~~ (Vis e k2).
Proof.
  intros. pcofix CIH.
  pfold. constructor.
  - split; intro; apply finite_taus_vis.
  - intros. inversion UNTAUS1. inversion UNTAUS2. subst.
    constructor. intro. exfalso. apply H. apply exists_inhabited with (P:=fun x => True). exists x. auto.
Qed.

Lemma traces_equiv_finite_taus : forall {E R} (t1 t2 : itree E R),
    (forall t r, is_trace t1 t r <-> is_trace t2 t r) ->
    finite_taus t1 -> finite_taus t2.
Proof.
  intros. red in H0. decompose [ex] H0; clear H0. induction H2; subst.
  - rewrite (itree_eta t) in *. destruct (observe t).
    + assert (is_trace (Ret r : itree E R) [] (Some r)) by constructor.
      rewrite H in H0. remember (Some r) as r'.
      induction H0; inversion Heqr'; subst.
      * apply finite_taus_ret.
      * rewrite finite_taus_tau. apply IHis_trace; auto. intros.
        symmetry. apply is_trace_tau_iff. symmetry. apply H.
      * apply finite_taus_vis.
    + inversion PROP.
    + assert (is_trace (Vis e k) [OutputEvent e] None) by constructor.
      rewrite H in H0.
      remember [OutputEvent e] as l in H0. induction H0; try solve [inversion Heql]; subst.
      * rewrite finite_taus_tau. apply IHis_trace; auto. intros.
        symmetry. apply is_trace_tau_iff. symmetry. apply H.
      * apply finite_taus_vis.
(* destruct (classic (inhabited u)). *)
(*       { *)
(*         inversion H0. *)
(*         assert (is_trace (Vis e k) [Event e X] None) by repeat constructor. *)
(*         rewrite H in H1. remember [Event e X] as l. *)
(*         induction H1; inversion Heql; subst. *)
(*         - apply finite_taus_tau. apply IHis_trace; auto. intros. *)
(*           symmetry. apply is_trace_tau_iff. symmetry. apply H. *)
(*         - apply finite_taus_vis. *)
(*       } *)
(*       { *)
(*         assert (is_trace (Vis e k) [OutputEvent e] None) by constructor. *)
(*         rewrite H in H1. *)
(*         remember [OutputEvent e] as l in H1. induction H1; try solve [inversion Heql]; subst. *)
(*         - rewrite finite_taus_tau. apply IHis_trace; auto. intros. *)
(*           symmetry. apply is_trace_tau_iff. symmetry. apply H. *)
(*         - apply finite_taus_vis. *)
(*       } *)
  - apply IHuntaus. intros. apply is_trace_tau_iff. auto.
Qed.

Lemma eutt_traces: forall {E R} (t1 t2 : itree E R),
    eutt t1 t2 ->
    (forall t r, is_trace t1 t r <-> is_trace t2 t r).
Proof.
  intros. split; intros.
  - apply (eutt_is_trace _ _ _ _ H H0).
  - apply Symmetric_eutt in H. apply (eutt_is_trace _ _ _ _ H H0).
Qed.

Lemma unalltaus_tau_false: forall {E R} n (t t' : itree E R), unalltaus n t (Tau t') -> False.
Proof.
  intros. remember (Tau t') as t''. induction H; subst; auto.
Qed.


Lemma traces_eutt: forall {E R} (t1 t2 : itree E R),
    (forall t r, is_trace t1 t r <-> is_trace t2 t r) ->
    eutt t1 t2.
Proof.
  intros E R.
  pcofix CIH. intros t1 t2 Hiff. pfold. constructor.
  - split.
    + apply traces_equiv_finite_taus; auto.
    + symmetry in Hiff. apply traces_equiv_finite_taus; auto.
  - intros. assert (Hiff': forall t r, is_trace t1' t r <-> is_trace t2' t r).
    { intros. split; intros.
      - pose proof (is_trace_unalltaus' _ _ _ _ _ H UNTAUS1).
        rewrite Hiff in H0. eapply is_trace_unalltaus; eauto.
      - pose proof (is_trace_unalltaus' _ _ _ _ _ H UNTAUS2).
        rewrite <- Hiff in H0. eapply is_trace_unalltaus; eauto.
    }
    rewrite (itree_eta t1') in *. rewrite (itree_eta t2') in *.
    destruct (observe t1') in *; destruct (observe t2');
      try solve [contradiction (unalltaus_tau_false _ _ _ UNTAUS1)];
      try solve [contradiction (unalltaus_tau_false _ _ _ UNTAUS2)].
    + assert (is_trace (Ret r0 : itree E R) [] (Some r0)) by constructor.
      rewrite Hiff' in H. inversion H; subst. constructor.
    + assert (is_trace (Ret r0 : itree E R) [] (Some r0)) by constructor.
      rewrite Hiff' in H. inversion H.
    + assert (is_trace (Ret r0 : itree E R) [] (Some r0)) by constructor.
      rewrite <- Hiff' in H. inversion H.
    + (* destruct (classic (inhabited u)). *)
      (* * destruct H. assert (is_trace (Vis e k) [Event e X] None) by (repeat constructor). *)
      (*   rewrite Hiff' in H. inversion H; subst. invert_existTs; subst. *)
      (*   constructor. *)
      (*   intros. right. apply CIH. intros. split; intros. *)
      (*   { assert (is_trace (Vis e k) ((Event e x) :: t) r0) by (constructor; auto). *)
      (*     rewrite Hiff' in H1. inversion H1; auto. invert_existTs; subst; auto. *)
      (*   } *)
      (*   { assert (is_trace (Vis e k0) ((Event e x) :: t) r0) by (constructor; auto). *)
      (*     rewrite <- Hiff' in H1. inversion H1; auto. invert_existTs; subst; auto. *)
      (*   } *)
      (* *  *)
      assert (is_trace (Vis e k) [OutputEvent e] None) by (constructor; auto).
      rewrite Hiff' in H. inversion H; subst. invert_existTs; subst.
      constructor. intros.
      right. apply CIH. intros. split; intros.
      { assert (is_trace (Vis e k) ((Event e x) :: t) r0) by (constructor; auto).
        rewrite Hiff' in H1. inversion H1; auto. invert_existTs; subst; auto.
      }
      { assert (is_trace (Vis e k0) ((Event e x) :: t) r0) by (constructor; auto).
        rewrite <- Hiff' in H1. inversion H1; auto. invert_existTs; subst; auto.
      }

      (* exfalso. apply H. *)
      (* apply exists_inhabited with (P:=fun x => True). exists x. auto. *)
Qed.

Lemma final: forall {E R} (t1 t2 : itree E R),
    t1 ~~ t2 <->
    (forall t r, is_trace t1 t r <-> is_trace t2 t r).
Proof.
  intros. split; intro.
  - apply eutt_traces; auto.
  - apply traces_eutt; auto.
Qed.

(* counterexample for old defn of is_trace *)
Lemma is_trace_but_not_eutt : forall {E R} (X : Type) (e : E X) (k : X -> itree E R),
    (~inhabited X) ->
    (forall t r, is_trace ITree.spin t r <-> is_trace (Vis e k) t r)
.
Proof.
  intros. split; intro.
  - remember ITree.spin as tree. induction H0.
    + constructor.
    + unfold ITree.spin in Heqtree. rewrite itree_eta in Heqtree. inversion Heqtree.
    + apply IHis_trace. rewrite itree_eta in Heqtree. inversion Heqtree. reflexivity.
    + unfold ITree.spin in Heqtree. rewrite itree_eta in Heqtree. inversion Heqtree.
    + (* this last case does not exist for old defn of traces *)
        unfold ITree.spin in Heqtree. rewrite itree_eta in Heqtree. inversion Heqtree.
  - remember (Vis e k) as tree. induction H0; try inversion Heqtree; subst.
    + constructor.
    + exfalso. apply H. apply exists_inhabited with (P:=fun _ => True). exists x. auto.
    + invert_existTs; subst.
Abort.

Lemma is_trace_prefix: forall {E R} (t : itree E R) tr1 tr2 r,
    is_trace t (tr1 ++ tr2) r ->
    exists r', is_trace t tr1 r'.
Proof.
  intros. remember (tr1 ++ tr2) as tr. revert tr1 tr2 Heqtr. induction H; intros.
  - destruct tr1.
    + exists None. constructor.
    + inversion Heqtr.
  - destruct tr1.
    + exists None. constructor.
    + inversion Heqtr.
  - destruct (IHis_trace _ _ Heqtr). eexists. constructor. eassumption.
  - destruct tr1.
    + exists None. constructor.
    + inversion Heqtr. destruct e0; inversion H1. subst. invert_existTs. subst.
      destruct (IHis_trace _ _ eq_refl).
      eexists. constructor. eauto.
  - exists None. destruct tr1.
    + constructor.
    + inversion Heqtr. destruct e0; inversion H0.
      subst. invert_existTs. subst.
      destruct tr1.
      * constructor.
      * inversion H1.
Qed.
