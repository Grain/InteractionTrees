(* From interaction trees you can define semantics in an "up-to" style.
 *
 * With interaction trees, you need to maintain the effects so the output
 * that you get is an inductive interaction tree with an extra
 * `Unknown`/`OutOfFuel` constructor. This is analogous to the need to
 * maintain the trace in a trace-based semantics.
 *)
Require Import Coq.Classes.RelationClasses.

From ITree Require Import
     Core OpenSum.

Section with_effects.
  Variable E : Type -> Type.

  Inductive Eff {t : Type} : Type :=
  | Ret (_ : t)
  | Vis {u} (_ : E u) (_ : u -> Eff)
  | Unknown.
  Arguments Eff _ : clear implicits.

  (* `EffLe a b` when `a` is a "prefix" of `b`
   *)
  Inductive EffLe {t} : Eff t -> Eff t -> Prop :=
  | EffLe_Any : forall b, EffLe Unknown b
  | EffLe_Ret : forall a, EffLe (Ret a) (Ret a)
  (* switching order of k1 k2 causes an inversion bug (?) *)
  | EffLe_Vis : forall u (e : E u) k2 k1,
      (forall x, EffLe (k1 x) (k2 x)) ->
      EffLe (Vis e k1) (Vis e k2).

  Global Instance Reflexive_EffLe {t} : Reflexive (@EffLe t).
  Proof. compute. induction x; constructor; eauto. Qed.

  Lemma EffLe_inj_Vis:
    forall (t : Type) (z : Eff t) (u : Type) (e : E u) (k2 : u -> Eff t),
      EffLe (Vis e k2) z ->
      exists k : u -> Eff t, z = Vis e k /\ (forall x : u, EffLe (k2 x) (k x)).
  Proof.
    intros t z u e k2 H1.
    refine
      match H1 in EffLe a b
            return match a  return Prop with
                   | Vis e' k' => _
                   | _ => True
                   end
      with
      | EffLe_Vis _ _ _ _ keq =>
        ex_intro _ _ (conj eq_refl keq)
      | _ => I
      end.
  Defined.

  Global Instance Transitive_EffLe {t} : Transitive (@EffLe t).
  Proof. compute. intros x y z H; revert z.
         induction H; simpl; intros; eauto; try econstructor.
         eapply EffLe_inj_Vis in H1.
         destruct H1 as [ ? [ ? ? ] ].
         subst. constructor.
         intros. eapply H0. eauto.
  Qed.

End with_effects.

Arguments Eff _ _ : clear implicits.
Arguments Ret {_} [_] _.
Arguments Vis {_ _ _} _ _.
Arguments Unknown {_ _}.
Arguments EffLe {_ _} _ _.

Section upto.
  Variable E : Type -> Type.

  Inductive Approx {t} (it : itree E t) : Eff E t -> Prop :=
  | A_Unknown : Approx it Unknown
  | A_Ret     : forall v z,
      it.(observe) = RetF v ->
      Approx it z
  | A_Vis     : forall {u} (e : E u) k1 k2,
      it.(observe) = VisF e k1 ->
      (forall x, Approx (k1 x) (k2 x)) ->
      Approx it (Vis e k2)
  | A_Tau     : forall it' e,
      it.(observe) = TauF it' ->
      Approx it' e ->
      Approx it e.

  Fixpoint upto {t} (n : nat) (i : itree E t) {struct n}
  : Eff E t :=
    match n with
    | 0 => Unknown
    | S n => match i.(observe) with
            | ITree.Core.RetF t => Ret t
            | ITree.Core.VisF e k => Vis e (fun x => upto n (k x))
            | ITree.Core.TauF k => upto n k
            end
    end.

  Theorem Approx_upto : forall t n (it : itree E t),
      Approx it (upto n it).
  Proof.
    induction n; simpl.
    - constructor.
    - intro it. simpl. destruct (observe it) eqn:Heq.
      + eapply A_Ret. eassumption.
      + eapply A_Tau. eassumption. eapply IHn.
      + eapply A_Vis; [ eassumption | ]. eauto.
  Qed.

  Lemma EffLe_upto : forall n t (a : itree E t),
      EffLe (upto n a) (upto (S n) a).
  Proof.
    induction n; simpl; intros.
    - constructor.
    - destruct (observe a); try constructor; eauto.
  Qed.

  Lemma EffLe_upto_strong
  : forall n m, n < m ->
           forall t (a : itree E t),
             EffLe (upto n a) (upto m a).
  Proof.
    induction 1.
    - eapply EffLe_upto.
    - intros. etransitivity. eapply IHle. eapply EffLe_upto.
  Qed.

End upto.

Arguments upto {_} {_} _ _.

Section traces.
  Require Import
          ITree.Trace
          ITree.Eq.Eq
          ITree.Eq.UpToTaus
          Paco.paco
          Coq.Lists.List
          ProofIrrelevance.
  Import ListNotations.

  Ltac invert_existTs :=
    repeat match goal with
           | [ H : existT ?P ?p _ = existT ?P ?p _ |- _ ] => apply inj_pair2 in H
           end; subst.

  Variable E : Type -> Type.
  Variable R : Type.

  Definition Eff_incl (t1 t2 : itree E R) : Prop :=
    forall n, exists m, EffLe (upto n t1) (upto m t2).
  Definition Eff_eq (t1 t2 : itree E R) : Prop :=
    Eff_incl t1 t2 /\ Eff_incl t2 t1.

  (* Lemma test : forall (X : Type) n (e : E X) (k1 k2 : X -> itree E R), *)
  (*     (exists m, forall x, EffLe (upto n (k1 x)) (upto m (k2 x))) -> *)
  (*     (exists m, EffLe (Vis e (fun x => (upto n (k1 x)))) (Vis e (fun x => (upto m (k2 x))))). *)
  (* Proof. *)
  (*   intros. destruct H as [m ?]. exists m. *)
  (*   constructor. assumption. *)
  (* Qed. *)

  (* Global Instance Transitive_EffLe {t} : Transitive (@EffLe t). *)
  (* Proof. *)
  (*   compute. induction x, y; intros; *)
  (*              try solve [inv H; auto]; *)
  (*              try solve [inv H0; auto]; *)
  (*              try solve [constructor]. *)
  (*   inv H0. inv H1. invert_existTs. constructor. intros. eapply H; eauto. *)
  (* Qed. *)

  Global Instance Reflexive_Eff_incl : Reflexive Eff_incl.
  Proof.
    do 2 red. intros.
    exists n. reflexivity.
    (* generalize dependent t. induction n; intros. *)
    (* - exists 1. constructor. *)
    (* - simpl. destruct (observe t) eqn:Heqt; auto. *)
    (*   + exists 1. simpl. rewrite Heqt. constructor. *)
    (*   + destruct (IHn t0) as [m ?]. *)
    (*     exists (S m). simpl. rewrite Heqt; assumption. *)
    (*   + destruct (IHn t) as [m ?]. *)
    (*     exists (S m). simpl. rewrite Heqt. constructor. intros. *)
    (* TODO ISSUE HERE *)
  Qed.

  Global Instance Transitive_Eff_incl : Transitive Eff_incl.
  Proof.
    do 2 red. intros.
    (* etransitivity. apply H. apply H0. *)
    destruct (H n) as [m ?].
    destruct (H0 m) as [m' ?].
    exists m'. etransitivity; eauto.
  Qed.
  (* Lemma Eff_incl_Ret : forall r (t : itree E R), *)
  (*     Eff_incl (Core.Ret r) t -> *)
  (*     t ≅ Core.Ret r. *)
  (* Proof. *)
  (*   intros. red in H. pcofix CIH. *)
  (*   pfold. destruct (H 1). simpl in H0. inversion H0; subst. destruct *)
  (* Qed. *)

  (* todo move this into the proof, since only used once *)
  Lemma upto_trace_ret : forall r n (t : itree E R),
      upto n t = Ret r ->
      is_trace t nil (Some r).
  Proof.
    intros. red. generalize dependent t.
    induction n; intros; inversion H; subst.
    destruct (observe t); inversion H1; constructor; auto.
  Qed.
  Lemma upto_trace_vis : forall (X : Type) (e : E X) k n (t : itree E R) (x : X),
      upto n t = Vis e k ->
      exists tr r, is_trace t ((Event e x) :: tr) r.
  Proof.
    intros.
    (* remember (observe t). *)
    generalize dependent t.
    induction n; intros; inv H.
    destruct (observe t) eqn:Heqt; inversion H1.
    - destruct (IHn t0 H0) as [tr [r ?]].
      exists tr, r. red. rewrite Heqt. constructor. auto.
    - subst. invert_existTs. exists [], None.
      red. rewrite Heqt. repeat constructor.
  Qed.

  (* Lemma test : forall X (t1 t2 : itree E R) (e : E X) (k : X -> itree E R), *)
  (*     Eff_incl t1 t2 -> *)
  (*     observe t1 = VisF e k -> *)
  (*     exists k', (forall x : X, Eff_incl (k x) (k' x)) /\ observe t2 = VisF e k'. *)
  (* Proof. *)
  (*   intros. red in H. *)
  (* Qed. *)

  Lemma Eff_incl_vis : forall X (t1 t2 : itree E R) (e : E X) (k1 k2 : X -> itree E R),
      Eff_incl t1 t2 ->
      observe t1 = VisF e k1 ->
      observe t2 = VisF e k2 ->
      forall x, Eff_incl (k1 x) (k2 x).
  Proof.
    intros. intro. destruct (H (S n)) as [m H']. simpl in H'. rewrite H0 in H'.
    destruct m; inversion H'. rewrite H1 in H6. inversion H6.
    invert_existTs.
    exists m. auto.
  Qed.

  Lemma Eff_incl_tau_add: forall (t1 t2 t2' : itree E R),
      Eff_incl t1 t2 ->
      observe t2' = TauF t2 ->
      Eff_incl t1 t2'.
  Proof.
    intros. intro. destruct (H n) as [m H'].
    exists (S m). simpl. rewrite H0. auto.
  Qed.
  Lemma Eff_incl_tau_remove: forall (t1 t2 t2' : itree E R),
      Eff_incl t1 t2 ->
      observe t2 = TauF t2' ->
      Eff_incl t1 t2'.
  Proof.
    intros. intro. destruct (H n) as [m H'].
    destruct m.
    - simpl in H'. inversion H'. exists 0. constructor.
    - simpl in H'. rewrite H0 in H'. exists m. auto.
  Qed.

  Lemma Eff_incl_unalltaus: forall (t1 t2 t2' : itree E R),
      Eff_incl t1 t2 ->
      unalltaus t2 t2' ->
      Eff_incl t1 t2'.
  Proof.
    intros ? ? ? ? [? ?].
    remember (observe t2). remember (observe t2').
    generalize dependent t2.
    induction H0; intros; subst.
    - intro. destruct (H n). destruct x; simpl in H0.
      + inversion H0. exists 0. constructor.
      + rewrite <- Heqi in H0. exists (S x). assumption.
    - eapply IHuntausF; auto. eapply Eff_incl_tau_remove; eauto.
  Qed.

  Lemma Eff_incl_vis1: forall X (t1 t2 : itree E R) (e : E X) (k : X -> itree E R),
      Eff_incl t1 t2 ->
      observe t1 = VisF e k ->
      exists t2', unalltaus t2 t2' /\ (exists k', observe t2' = VisF e k').
  Proof.
    intros. destruct (H 1) as [m H'].
    simpl in H'. rewrite H0 in H'. inversion H'. invert_existTs.
    clear H'. generalize dependent e. generalize dependent t2.
    induction m; intros; inversion H5. destruct (observe t2) eqn:?; inversion H3.
    - pose proof (Eff_incl_tau_remove _ _ _ H Heqi). specialize (IHm t H1 _ H0 H3).
      destruct IHm as [? [? ?]].
      exists x. split; auto. rewrite <- Heqi. eapply unalltaus_tau'; eauto.
    - subst. invert_existTs. exists (Core.Vis e0 k0). split; auto.
      + constructor; auto. eapply notau_vis; simpl; eauto.
      + exists k0. auto.
  Qed.

  Lemma Eff_incl_trace_incl : forall (t1 t2 : itree E R),
      Eff_incl t1 t2 ->
      trace_incl t1 t2.
  Proof.
    do 2 red. intros. red in H0. (* red in H. *)
    remember (observe t1) as o1. (* remember tr as tr'. remember r_ as r'. *)
    generalize dependent t1. generalize dependent t2.
    induction H0; intros; subst; try constructor.
    - destruct (H 1) as [m Hupto]. simpl in Hupto. rewrite <- Heqo1 in Hupto.
      inv Hupto.
      symmetry in H2. eapply upto_trace_ret; eauto.
    - apply IHis_traceF with (t1:=t); auto. intro. specialize (H (S n)).
      simpl in H. rewrite <- Heqo1 in H. auto.
    - symmetry in Heqo1. destruct (Eff_incl_vis1 _ _ _ _ _ H Heqo1) as [? [? [? ?]]].
      pose proof (Eff_incl_unalltaus _ _ _ H H1) as H'.
      destruct H1.
      remember (observe x0).
      induction H1; intros; subst.
      + rewrite H2. constructor. apply IHis_traceF with (t1:=(k x)); auto.
        apply (Eff_incl_vis _ _ _ _ _ _ H' Heqo1); auto.
      + constructor. apply IHuntausF; auto.
    - symmetry in Heqo1. destruct (Eff_incl_vis1 _ _ _ _ _ H Heqo1) as [? [? [? ?]]].
      pose proof (Eff_incl_unalltaus _ _ _ H H0) as H'.
      destruct H0.
      remember (observe x).
      induction H0; intros; subst.
      + rewrite H1. constructor.
      + constructor. apply IHuntausF; auto.
  Qed.

  Lemma exists_Sm: forall (e : Eff E R) (t : itree E R),
      (exists m, EffLe e (upto (S m) t)) ->
      exists m, EffLe e (upto m t).
  Proof.
    intros. destruct H as [m ?].
    exists (S m). assumption.
  Qed.

  Lemma upto_unknown : forall n (t1 : itree E R),
      upto (S n) t1 = Unknown ->
      upto n t1 = Unknown.
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl in *. destruct (observe t1) eqn:Heqt1; try solve [inversion H].
      apply IHn. auto.
  Qed.


  Lemma EffLe_upto_succ : forall n m (t1 t2 : itree E R),
      EffLe (upto n t1) (upto m t2) ->
      EffLe (upto n t1) (upto (S m) t2).
  Proof.
    induction n.
    - constructor.
    - induction m; intros.
      { inversion H. simpl. rewrite <- H1. constructor. }
      {
        simpl in *. destruct (observe t1) eqn:Heqt1; auto.
        - clear IHn.
          destruct (observe t2) eqn:Heqt2; auto.
          + specialize (IHm t1 t).
            rewrite Heqt1 in IHm. apply IHm; auto.
          + inversion H.
        - clear IHm.
          destruct (observe t2) eqn:Heqt2; auto.
          specialize (IHn (S m) t t2).
          simpl in IHn. rewrite Heqt2 in IHn. apply IHn. auto.
        - destruct (observe t2) eqn:Heqt2; auto.
          + specialize (IHm t1 t).
            rewrite Heqt1 in IHm. apply IHm; auto.
          + clear IHm.
            inversion H. subst. invert_existTs. constructor. intros.
            apply IHn. auto.
      }
  Qed.

  Lemma EffLe_upto_pred : forall n m (t1 t2 : itree E R),
    EffLe (upto (S n) t1) (upto m t2) ->
    EffLe (upto n t1) (upto m t2).
  Proof.
    induction n.
    - constructor.
    - induction m; intros.
      { rewrite upto_unknown. constructor. inversion H. auto. }
      {
        simpl in *. destruct (observe t1) eqn:Heqt1; auto.
        - clear IHm.
          destruct (observe t2) eqn:Heqt2; auto;
            specialize (IHn (S m) t t2);
            simpl in IHn;
            rewrite Heqt2 in IHn;
            apply IHn; auto.
        - destruct (observe t2) eqn:Heqt2; auto.
          + inversion H.
          + specialize (IHm t1 t). rewrite Heqt1 in IHm. auto.
          + clear IHm.
            inversion H. subst. invert_existTs. constructor. intros. auto.
      }
  Qed.

  (* Lemma test : forall n m (t1 t2 : itree E R), *)
  (*   EffLe (upto (S n) t1) (upto m t2) -> *)
  (*   EffLe (upto n t1) (upto (S m) t2). *)
  (* Proof. *)
  (*   intros n m. revert n. *)
  (*   induction m; intros. *)
  (*   - inversion H. symmetry in H1. apply upto_unknown in H1. rewrite H1. constructor. *)
  (*   - simpl. *)
  (* Admitted. *)

  Lemma test_constructor : forall (X : Type) (e : E X) (k1 k2 : X -> itree E R) n,
      (forall x : X, exists m,
            EffLe (upto n (k1 x))
                  (upto m (k2 x))) ->
      (exists m,
          EffLe (Vis e (fun x => upto n (k1 x)))
                (Vis e (fun x => upto m (k2 x)))).
  Proof.
    intros.
    (* generalize dependent k1. generalize dependent k2. generalize dependent e. *)
    induction n; intros.
    - exists 1. constructor. intros. constructor.
    - assert (forall x : X, exists m : nat, EffLe (upto n (k1 x)) (upto m (k2 x))). {
        intros. destruct (H x) as [m ?]. exists m. apply EffLe_upto_pred; auto.
      }
      destruct (IHn H0) as [m ?]. exists m.
  Abort.

  Lemma trace_incl_Eff_incl : forall (t1 t2 : itree E R),
      trace_incl t1 t2 ->
      Eff_incl t1 t2.
  Proof.
    red. intros. red in H.
    generalize dependent t1. generalize dependent t2.
    induction n; intros.
    - exists 0. constructor.
    - unfold is_trace in *. simpl. destruct (observe t1) eqn:Heqt1.
      + assert (is_traceF (RetF r : itreeF E R (itree E R)) [] (Some r)) by constructor.
        specialize (H _ _ H0).
        remember []. remember (Some r). remember (observe t2).
        generalize dependent t2.
        induction H; intros; try inversion Heql; try inversion Heqo; subst.
        * exists 1. simpl. rewrite <- Heqi. constructor.
        * destruct (IHis_traceF eq_refl eq_refl H0 t eq_refl) as [m ?].
          exists (S m). simpl. rewrite <- Heqi. auto.
      + apply IHn. intros.  apply H. constructor. assumption.
      + assert (observe t2 = VisF e k) by admit.
        apply exists_Sm. simpl. rewrite H0. apply test_constructor.
        intros.
        assert (trace_incl (k x) (k x)) by admit.
        apply (IHn _ _ H1).

        assert (is_traceF (VisF e k) [EventOut e] None) by constructor.
        specialize (H _ _ H0). inversion H.
        * admit.
        * simpl.

        apply test_constructor.

        (* eexists (S _). simpl. *)
        (* assert (is_traceF (VisF e k) [EventOut e] None) by constructor. *)
        (* specialize (H _ _ H0). inversion H. *)
        (* * admit. *)
        (* * invert_existTs. constructor. intros. *)
  Abort.

  Lemma eutt_Eff_incl : forall (t1 t2 : itree E R),
      t1 ≈ t2 ->
      Eff_incl t1 t2.
  Proof.
    red. intros.
    generalize dependent t1. generalize dependent t2.
    induction n; intros.
    - exists 1. constructor.
    - simpl. destruct (observe t1) eqn:Heqt1.
      + pinversion H.
        assert (finite_taus t1) by (eapply finite_taus_ret; eauto).
        inversion H0.
        rewrite FIN in H0. destruct H0.

        specialize (EQV _ _ H1 H0).
        destruct H0.
        remember (observe t2).
        admit.
        (* induction H0; intros; subst. *)
        (* * exists 1. simpl. destruct (observe t2) eqn:Heqt2; inversion H2. *)

      + apply IHn; auto. rewrite <- H. symmetry. apply tauF_eutt. symmetry. auto.
      + pinversion H.
        assert (finite_taus t1) by (eapply finite_taus_vis; eauto).
        inversion H0.
        rewrite FIN in H0. destruct H0 as [ot2 ?].
        specialize (EQV _ _ H1 H0).
        rewrite Heqt1 in H1. inversion H1. inversion H2; subst.
        * inversion EQV. invert_existTs.
          assert (observe t2 = VisF e k2) by admit.
          apply exists_Sm. simpl. rewrite H4.
          apply test.
          assert (forall x, exists m, EffLe (upto n (k x)) (upto m (k2 x))). {
            intros.
            apply IHn. pclearbot. apply H8.
          }

          eexists. constructor.
          intros. apply H4.



(* Attempt to reproduce bug *)
(* Inductive ASDF {E : Type -> Type} : Type := *)
(* | Vis {u} (_ : E u) (_ : u -> ASDF). *)
(* Inductive ASDF_Eq {E : Type -> Type} : ASDF -> ASDF -> Prop := *)
(* | ASDF1: forall u (e : E u) k2 k1, *)
(*     (forall x, ASDF_Eq (k1 x) (k2 x)) -> *)
(*     ASDF_Eq (Vis e k1) (Vis e k2). *)

(* Lemma test : forall E U (e : E U) (k1 k2 : U -> ASDF), *)
(*     ASDF_Eq (Vis e k1) (Vis e k2) -> *)
(*     False. *)
(* Proof. *)
(*   intros. inversion H. invert_exists. *)

End traces.
