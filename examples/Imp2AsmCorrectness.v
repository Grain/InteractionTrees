Require Import Imp Asm Imp2Asm.

Require Import Psatz.

From Coq Require Import
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ITree Require Import
     Basics_Functions
     Effect.Env
     ITree.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Programming.Show
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.

Section denote_list.

  Import MonadNotation.

  Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
    fix traverse__ l: M unit :=
      match l with
      | [] => ret tt
      | a::l => (f a;; traverse__ l)%monad
      end.

  Context {E} {EL : Locals -< E} {EM : Memory -< E}.

  Definition denote_list: list instr -> itree E unit :=
    traverse_ (denote_instr E).

  Lemma denote_after_denote_list:
    forall {label: Type} instrs (b: branch label),
      denote_block E (after instrs b) ≅ (denote_list instrs ;; denote_branch E b).
  Proof.
    induction instrs as [| i instrs IH]; intros b.
    - simpl; rewrite ret_bind; reflexivity.
    - simpl; rewrite bind_bind.
      eapply eq_itree_eq_bind; [reflexivity | intros []; apply IH].
  Qed.

  Lemma denote_list_app:
    forall is1 is2,
      @denote_list (is1 ++ is2) ≅
                   (@denote_list is1;; denote_list is2).
  Proof.
    intros is1 is2; induction is1 as [| i is1 IH]; simpl; intros; [rewrite ret_bind; reflexivity |].
    rewrite bind_bind; setoid_rewrite IH; reflexivity.
  Qed.

End  denote_list.

Section Correctness.

  (*
    Potential extensions for later:
    - Add some non-determinism at the source level, for instance order of evaluation in add, and have the compiler  an order.
    The correctness would then be a refinement.
     How to define it? Likely with respect to an oracle.
    - Add a print effect?
    - Change languages to map two notions of state at the source down to a single one at the target?
      Make the keys of the second env monad as the sum of the two initial ones.
   *)


  Import ITree.Core.

  Variable E: Type -> Type.
  Context {HasLocals: Locals -< E} {HasMemory: Memory -< E}.

  Lemma fmap_block_map:
    forall  {L L'} b (f: L -> L'),
      denote_block E (fmap_block f b) ≅ ITree.map (sum_bimap f id) (denote_block E b).
  Proof.
    induction b as [i b | br]; intros f.
    - simpl.
      unfold ITree.map; rewrite bind_bind.
      eapply eq_itree_eq_bind; [reflexivity | intros []; apply IHb].
    - simpl.
      destruct br; simpl.
      + unfold ITree.map; rewrite ret_bind; reflexivity.
      + unfold ITree.map; rewrite bind_bind.
        eapply eq_itree_eq_bind; [reflexivity | intros []; rewrite ret_bind; reflexivity].
      + unfold ITree.map; rewrite ret_bind; reflexivity.
  Qed.

  Variant Rvar : var -> var -> Prop :=
  | Rvar_var v : Rvar (varOf v) v.

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Definition Renv (g_asm g_imp : alist var value) : Prop :=
    forall k_asm k_imp, Rvar k_asm k_imp ->
                   forall v, alist_In k_imp g_imp v <-> alist_In k_asm g_asm v.

  (* Let's not unfold this inside of the main proof *)
  Definition sim_rel g_asm n: alist var value * unit -> alist var value * value -> Prop :=
    fun '(g_asm', _) '(g_imp',v) =>
      Renv g_asm' g_imp' /\            (* we don't corrupt any of the imp variables *)
      alist_In (gen_tmp n) g_asm' v /\ (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            alist_In (gen_tmp m) g_asm v <-> alist_In (gen_tmp m) g_asm' v).

End Correctness.

Section EUTT.

  Require Import Paco.paco.

  Context {E: Type -> Type}.

  Instance eq_itree_run_env {E R} {K V map} {Mmap: Maps.Map K V map}:
    Proper (@eutt (envE K V +' E) R R eq ==> eq ==> @eutt E (prod map R) (prod map R) eq)
           (run_env R).
  Proof.
  Admitted.

End EUTT.

Section GEN_TMP.

  Lemma to_string_inj: forall (n m: nat), n <> m -> to_string n <> to_string m.
  Admitted.

  Lemma gen_tmp_inj: forall n m, m <> n -> gen_tmp m <> gen_tmp n.
  Proof.
    intros n m ineq; intros abs; apply ineq.
    apply to_string_inj in ineq; inversion abs; easy.
  Qed.

  Lemma varOf_inj: forall n m, m <> n -> varOf m <> varOf n.
  Proof.
    intros n m ineq abs; inv abs; easy.
  Qed.

End GEN_TMP.

Opaque gen_tmp.
Opaque varOf.

Section Real_correctness.

  Context {E': Type -> Type}.
  Context {HasMemory: Memory -< E'}.
  Definition E := Locals +' E'.

  Definition interp_locals {R: Type} (t: itree E R) (s: alist var value): itree E' (alist var value * R) :=
    run_env _ (interp1 evalLocals _ t) s.

  Instance eq_itree_interp_locals {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (alist var value) R) (prod _ R) eq)
           interp_locals.
  Proof.
  Admitted.

  Lemma interp_locals_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (s: alist var value),
      @eutt E' _ _ eq
            (interp_locals (ITree.bind t k) s)
            (ITree.bind (interp_locals t s) (fun s' => interp_locals (k (snd s')) (fst s'))).
  Admitted.

  Set Nested Proofs Allowed.

  Ltac force_left :=
    match goal with
    | |- eutt _ ?x _ => rewrite (itree_eta x); cbn
    end.

  Ltac force_right :=
    match goal with
    | |- eutt _ _ ?x => rewrite (itree_eta x); cbn
    end.

  Ltac untau_left := force_left; rewrite tau_eutt.
  Ltac untau_right := force_right; rewrite tau_eutt.

  Arguments alist_add {_ _ _ _}.
  Arguments alist_find {_ _ _ _}.

  Ltac flatten_goal :=
    match goal with
    | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac flatten_hyp h :=
    match type of h with
    | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac flatten_all :=
    match goal with
    | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
    | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
    end.

  Ltac inv h := inversion h; subst; clear h.
  Arguments alist_remove {_ _ _ _}. 

  Lemma In_add_eq {K V: Type} {RR:RelDec eq} {RRC:@RelDec_Correct _ _ RR}:
    forall k v (m: alist K V),
      alist_In k (alist_add k v m) v.
  Proof.
    intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
  Qed.

  (* A removed key is not contained in the resulting map *)
  Lemma not_In_remove:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v: V),
      ~ alist_In k (alist_remove k m) v.
  Proof.
    induction m as [| [k1 v1] m IH]; intros.
    - simpl; intros abs; inv abs. 
    - simpl; flatten_goal.
      + unfold alist_In; simpl.
        rewrite Bool.negb_true_iff in Heq; rewrite Heq.
        intros abs; eapply IH; eassumption.
      + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        intros abs; eapply IH; eauto. 
  Qed.

  (* Removing a key does not alter other keys *)
  Lemma In_In_remove_ineq:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_remove k' m) v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
    simpl.
    flatten_goal.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
      flatten_goal; auto.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
      flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
  Qed.       

  Lemma In_remove_In_ineq:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      alist_In k (alist_remove k' m) v ->
      alist_In k m v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
    simpl in IN; flatten_hyp IN.
    - unfold alist_In in *; simpl in *.
      flatten_all; auto.
      eapply IH; eauto.
    -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
     unfold alist_In; simpl. 
     flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
     exfalso; eapply not_In_remove; eauto.
     eapply IH; eauto.
  Qed.       

  Lemma In_remove_In_ineq_iff:
    forall (K V : Type) {RR: RelDec eq} {RRC:@RelDec_Correct _ _ RR}
      (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k (alist_remove k' m) v <->
      alist_In k m v.
  Proof.
    intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
  Qed.       

  (* Adding a value to a key does not alter other keys *)
  Lemma In_In_add_ineq {K V: Type} {RR: RelDec eq} `{RRC:@RelDec_Correct _ _ RR}:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_add k' v' m) v.
  Proof.
    intros.
    unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
    apply In_In_remove_ineq; auto.
  Qed.

  Lemma In_add_In_ineq {K V: Type} {RR: RelDec eq} `{RRC:@RelDec_Correct _ _ RR}:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k (alist_add k' v' m) v ->
      alist_In k m v. 
  Proof.
    intros k v k' v' m ineq IN.
    unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
    eapply In_remove_In_ineq; eauto.
  Qed.

  Lemma In_add_ineq_iff {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}:
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      alist_In k m v <-> alist_In k (alist_add k' v' m) v.
  Proof.
    intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
  Qed.

  (* alist_find fails iff no value is associated to the key in the map *)
  Lemma alist_find_None {K V: Type} `{RR: RelDec _ (@eq K)} `{RRC:@RelDec_Correct _ _ RR}:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Proof.
    induction m as [| [k1 v1] m IH]; [simpl; easy |].
    simpl; split; intros H. 
    - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
      apply (H v1); left; reflexivity.
      apply IH; intros v abs; apply (H v); right; assumption.
    - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
      intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
  Qed.

  Lemma Renv_add: forall g_asm g_imp n v,
      Renv g_asm g_imp -> Renv (alist_add (gen_tmp n) v g_asm) g_imp.
  Proof.
    repeat intro.
    destruct (k_asm ?[ eq ] (gen_tmp n)) eqn:EQ.
    rewrite rel_dec_correct in EQ; subst; inv H0.
    rewrite <- neg_rel_dec_correct in EQ.
    rewrite (H _ _ H0).
    apply In_add_ineq_iff; auto.
  Qed.

  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_asm g_imp ->
      alist_find x g_imp = alist_find (varOf x) g_asm.
  Proof.
    intros.
    destruct (alist_find x g_imp) eqn:LUL, (alist_find (varOf x) g_asm) eqn:LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - eapply H in LUL; [| constructor].
      rewrite LUL in LUR; auto.
    - erewrite <- (H (varOf x) x (Rvar_var x) v) in LUR.
      rewrite LUR in LUL; inv LUL.
  Qed.      

  Lemma sim_rel_add: forall g_asm g_imp n v,
      Renv g_asm g_imp ->
      sim_rel g_asm n (alist_add (gen_tmp n) v g_asm, tt) (g_imp, v).
  Proof.
    intros.
    split; [| split].
    - apply Renv_add; assumption.
    - apply In_add_eq.
    - intros m LT v'.
      apply In_add_ineq_iff, gen_tmp_inj; lia.
  Qed.

  Lemma sim_rel_Renv: forall g_asm n s1 v1 s2 v2,
      sim_rel g_asm n (s1,v1) (s2,v2) -> Renv s1 s2.
  Proof.
    intros ? ? ? ? ? ? H; apply H.
  Qed.

  Lemma sim_rel_find_tmp_n:
    forall g_asm n g_asm' g_imp' v,
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_In (gen_tmp n) g_asm' v.
  Proof.
    intros ? ? ? ? ? [_ [H _]]; exact H. 
  Qed.

  Lemma sim_rel_find_tmp_lt_n:
    forall g_asm n m g_asm' g_imp' v,
      m < n ->
      sim_rel g_asm n (g_asm', tt) (g_imp',v) ->
      alist_find (gen_tmp m) g_asm = alist_find (gen_tmp m) g_asm'.
  Proof.
    intros ? ? ? ? ? ? ineq [_ [_ H]].
    match goal with
    | |- _ = ?x => destruct x eqn:EQ
    end.
    setoid_rewrite (H _ ineq); auto.
    match goal with
    | |- ?x = _ => destruct x eqn:EQ'
    end; [| reflexivity].
    setoid_rewrite (H _ ineq) in EQ'.
    rewrite EQ' in EQ; easy.
  Qed.

  Notation "(% x )" := (gen_tmp x) (at level 1).

  Lemma compile_expr_correct : forall e g_imp g_asm n,
      Renv g_asm g_imp ->
      eutt (sim_rel g_asm n)
           (interp_locals (denote_list (compile_expr n e)) g_asm)
           (interp_locals (denoteExpr e) g_imp).
  Proof.
    induction e; simpl; intros.
    - repeat untau_left.
      repeat untau_right.
      force_left; force_right.
      apply eutt_Ret.
      erewrite <- Renv_find; [| eassumption].
      apply sim_rel_add; assumption.
    - repeat untau_left.
      force_left.
      force_right.
      apply eutt_Ret.
      apply sim_rel_add; assumption.
    - do 2 setoid_rewrite denote_list_app.
      do 2 setoid_rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      + eapply IHe1; assumption.
      + intros [g_asm' []] [g_imp' v] HSIM.
        eapply eutt_bind_gen.
        eapply IHe2.
        eapply sim_rel_Renv; eassumption.
        intros [g_asm'' []] [g_imp'' v'] HSIM'.
        repeat untau_left.
        force_left; force_right.
        simpl fst in *.
        apply eutt_Ret.
        {
          generalize HSIM; intros LU; apply sim_rel_find_tmp_n in LU.
          unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto; fold (alist_In (%n) g_asm'' v) in LU.
          generalize HSIM'; intros LU'; apply sim_rel_find_tmp_n in LU'.
          rewrite LU,LU'.
          split; [| split].
          {
            eapply Renv_add, sim_rel_Renv; eassumption.
          }
          {
            apply In_add_eq.
          }
          {
            intros m LT v''.
            rewrite <- In_add_ineq_iff; [| apply gen_tmp_inj; lia].
            destruct HSIM as [_ [_ HSIM]].
            destruct HSIM' as [_ [_ HSIM']].
            rewrite HSIM; [| auto with arith].
            rewrite HSIM'; [| auto with arith].
            reflexivity.
          }
        }
  Qed.

  Lemma Renv_write_local:
    forall (x : Imp.var) (a a0 : alist var value) (v : Imp.value),
      Renv a a0 -> Renv (alist_add (varOf x) v a) (alist_add x v a0).
  Proof.
    intros k m m' v.
    repeat intro.
    red in H.
    specialize (H k_asm k_imp H0 v0).
    inv H0.
    unfold alist_add, alist_In; simpl.
    do 2 flatten_goal;
      repeat match goal with
             | h: _ = true |- _ => rewrite rel_dec_correct in h
             | h: _ = false |- _ => rewrite <- neg_rel_dec_correct in h
             end; try subst.
    - tauto.
    - tauto.
    - apply varOf_inj in Heq; easy.
    - setoid_rewrite In_remove_In_ineq_iff; eauto using RelDec_string_Correct.
Qed.

(** Correctness of compilation *)

  Lemma compile_assign_correct : forall e g_imp g_asm x,
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b))
           (interp_locals (denote_list (compile_assign x e)) g_asm)
           (interp_locals (v <- denoteExpr e ;; lift (SetVar x v)) g_imp).
  Proof.
    simpl; intros.
    unfold compile_assign.
    rewrite denote_list_app.
    do 2 rewrite interp_locals_bind.
    eapply eutt_bind_gen.
    eapply compile_expr_correct; eauto.
    intros.
    repeat untau_left.
    force_left.
    repeat untau_right; force_right.
    eapply eutt_Ret; simpl.
    destruct r1, r2.
    erewrite sim_rel_find_tmp_n; eauto; simpl.
    destruct H0.
    eapply Renv_write_local; eauto.
  Qed.

  Require Import Den.

  Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
    eq_den (denote_asm (seq_asm ab bc))
           (denote_asm ab >=> denote_asm bc).
  Proof.
  Admitted.

(* (incomplete) eutt modulo interp_locals and Renv on states *)
Axiom eq_den' : forall {A}, itree E A -> itree E A -> Prop.

  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm unit A) :
    eq_den' (denote_asm (if_asm e tp fp) tt)
            (denote_list e ;;
             v <- lift (GetVar tmp_if) ;;
             if v : value then denote_asm tp tt else denote_asm fp tt).
  Proof.
  Admitted.

  Lemma while_asm_correct (e : list instr) (p : asm unit unit) :
    eq_den' (denote_asm (while_asm e p) tt)
            (loop_den (fun l =>
               match l with
               | inl tt =>
                 denote_list e ;;
                 v <- lift (GetVar tmp_if) ;;
                 if v : value then
                   denote_asm p tt;; Ret (inl (inl tt))
                 else
                   Ret (inl (inr tt))
               | inr tt => Ret (inl (inl tt))
               end) tt).
  Proof.
  Admitted.

  Lemma compile_correct:
    forall s (g_imp g_asm : alist var value),
      Renv g_asm g_imp ->
      eutt (fun a b => Renv (fst a) (fst b) /\ snd a = snd b)
           (interp_locals (denote_asm (compile s) tt) g_asm)
           (interp_locals (denoteStmt s ;; Ret (inl tt)) g_imp).
    Proof.

      (*  Proof sketched on the old version of the theorem, mostly obsolete
    induction s; intros.
    { (* assign *)
      simpl.
      unfold denote_main. simpl. unfold denote_program.
      simpl.
      rewrite denote_after_denote_list.
      rewrite bind_bind.
      rewrite interp_locals_bind.
      rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      eapply compile_assign_correct; eauto.
      simpl; intros.
      clear - H0.
      rewrite fmap_block_map.
      unfold ITree.map.
      rewrite bind_bind.
      setoid_rewrite ret_bind.
      rewrite <- (bind_ret (interp_locals _ (fst r2))).
      rewrite interp_locals_bind.
      eapply eutt_bind_gen.
      { SearchAbout denote_block.
        instantiate (1 := fun a b => Renv (fst a) (fst b) /\ snd a = snd b).
        admit. }
      { simpl.
        intros.
        destruct r0, r3; simpl in *.
        destruct H; subst.
        destruct o0; simpl.
        { force_left.
          eapply Ret_eutt.
          simpl. tauto. }
        { force_left. eapply Ret_eutt; simpl. tauto. } } }
    { (* seq *)
      simpl.
      specialize (IHs1 _ (main (compile s2 b)) _ _ H).
      rewrite bind_bind.
      unfold denote_main; simpl.
      unfold denote_main in IHs1.
      rewrite fmap_block_map.
      unfold ITree.map. rewrite bind_bind.
      setoid_rewrite ret_bind.
*)

  Admitted.
     

(*
Seq a b
a :: itree _ Empty_set
[[Skip]] = Vis Halt ...
[[Seq Skip b]] = Vis Halt ...


[[s]] :: itree _ unit
[[a]] :: itree _ L (* if closed *)
*)


  (*

OBSOLETE?

Lemma interp_match_option : forall {T U} (x : option T) {E F} (h : E ~> itree F) (Z : itree _ U) Y,
    interp h match x with
             | None => Z
             | Some y => Y y
             end =
match x with
| None => interp h Z
| Some y => interp h (Y y)
end.
Proof. destruct x; reflexivity. Qed.
Lemma interp_match_sum : forall {A B U} (x : A + B) {E F} (h : E ~> itree F) (Z : _ -> itree _ U) Y,
    interp h match x with
             | inl x => Z x
             | inr x => Y x
             end =
match x with
| inl x => interp h (Z x)
| inr x => interp h (Y x)
end.
Proof. destruct x; reflexivity. Qed.

Lemma translate_match_sum : forall {A B U} (x : A + B) {E F} (h : E ~> F) (Z : _ -> itree _ U) Y,
    translate h match x with
             | inl x => Z x
             | inr x => Y x
             end =
match x with
| inl x => translate h (Z x)
| inr x => translate h (Y x)
end.
Proof. destruct x; reflexivity. Qed.
Lemma translate_match_option : forall {B U} (x : option B) {E F} (h : E ~> F) (Z : itree _ U) Y,
    translate h _ match x with
             | None => Z
             | Some x => Y x
             end =
match x with
| None => translate h Z
| Some x => translate h (Y x)
end.
Proof. destruct x; reflexivity. Qed.
*)



(* things to do?
 * 1. change the compiler to not compress basic blocks.
 *    - ideally we would write a separate pass that does that
 *    - split out each of the structures as separate definitions and lemmas
 * 2. need to prove `interp F (denote_block ...) = denote_block ...`
 * 3. link_seq_ok should be a proof by co-induction.
 * 4. clean up this file *a lot*
 * bonus: block fusion
 * bonus: break & continue
 *)

Lemma Proper_match : forall {T U V : Type} R (f f' : T -> V) (g g' : U -> V) x,
    ((pointwise_relation _ R) f f') ->
    ((pointwise_relation _ R) g g') ->
    R
    match x with
    | inl x => f x
    | inr x => g x
    end
    match x with
    | inl x => f' x
    | inr x => g' x
    end.
Proof. destruct x; compute; eauto. Qed.


End Real_correctness.

(*
Section tests.

  Import ImpNotations.

  Definition ex1: stmt :=
    "x" ← 1.

  (* The result is a bit annoying to read in that it keeps around absurd branches *)
  Compute (compile ex1).

  Definition ex_cond: stmt :=
    "x" ← 1;;;
    IF "x"
    THEN "res" ← 2
    ELSE "res" ← 3.

  Compute (compile ex_cond).

End tests.


*)