Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import Paco.paco.

Require ITree.ITree.
From Coq Require Import Arith.
From ITree Require Import ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Morphisms.
Require Import ITree.Fix.
Require Import ITree.OpenSum.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section MAP.
  (* Variables *)
  (*   (* (Key : Type) *) *)
  (*   (Value: Type) *)
  (*   (default: Value). *)

  Definition Key := nat.
  Definition Value := nat.
  Definition default := 0.

  (* the map "interface" *)
  Inductive IMap : Type -> Type :=
  | Read (k : Key) : IMap Value
  | Write (k : Key) (v : Value) : IMap unit.

  Definition State := Key -> Value.

  (* the map "operational semantics" *)
  Definition evalLocals' {eff} : eff_hom_s State IMap eff :=
    fun _ e st =>
      match e with
      | Read k =>
        ret (st, st k)
      | Write k v =>
        ret (fun k' => if Nat.eqb k k' then v else st k', tt)
      end.

  Definition init : State :=
    fun _ => default.

  Definition evalLocals t : itree emptyE (State * Value) :=
    interp_state evalLocals' t init.

  (* there was a typo in Freespec for the name of this *)
  Definition write_then_read (k : Key) (v : Value) : itree IMap Value :=
    lift (Write k v);;
    lift (Read k).

  Eval simpl in write_then_read.
  Eval simpl in (evalLocals (write_then_read 0 1)).

  (* Ltac simpl_itree := *)
  (*   cbv; repeat (rewrite match_itree at 1; f_equal; auto). *)

  Lemma write_then_read_example :
    exists s, eq_itree (evalLocals (write_then_read 0 1)) (Tau (Tau (Ret (s, 1)))).
  Proof.
    eexists. repeat (constructor; cbn).
  Qed.

  (* Lemma test' : eutt (evalLocals (write_then_read 0 1)) (Ret (fun x => match x with *)
  (*                                                                          | 0 => 1 *)
  (*                                                                          | _ => 0 *)
  (*                                                                          end, 1)). *)
  (* Proof.  *)
  (*   pfold. constructor; auto. *)
  (*   - rewrite test. split; intros. *)
  (*     + apply finite_taus_Ret. *)
  (*     + repeat rewrite finite_taus_Tau. apply finite_taus_Ret. *)
  (*   - intros. rewrite test in *. repeat rewrite unalltaus_tau in H. *)
  (*     apply unalltaus_notau_id in H; simpl; auto. *)
  (*     apply unalltaus_notau_id in H0; simpl; auto. *)
  (*     subst. constructor. *)
  (* Qed. *)

  (* Lemma write_then_read_neq : forall k k' v, *)
  (*     k <> k' -> *)
  (*     exists s, (evalLocals (write_then_read k v)) = Tau (Tau (Ret (s, v))). (* TODO *) *)
  (* Proof. *)
  (*   intros. eexists. simpl_itree. fold Nat.eqb. rewrite Nat.eqb_refl. auto. *)
  (* Qed. *)

End MAP.
