Require Import List.
Import ListNotations.

From ITree Require Import
     Core.

Inductive event (E : Type -> Type) : Type :=
| Event : forall X, E X -> X -> event E
| OutputEvent : forall X, E X -> event E
.

Arguments Event {E X}.
Arguments OutputEvent {E X}.

Definition trace (E : Type -> Type) : Type := list (event E).

Inductive is_trace {E : Type -> Type} {R : Type} :
  itree E R -> trace E -> option R -> Prop :=
| TraceEmpty : forall t, is_trace t [] None
| TraceRet : forall r, is_trace (Ret r) [] (Some r)
| TraceTau : forall t tr r_,
  is_trace t tr r_ ->
  is_trace (Tau t) tr r_
| TraceVis : forall X (e : E X) (x : X) k tr r_,
  is_trace (k x) tr r_ ->
  is_trace (Vis e k) (Event e x :: tr) r_
| TraceUninhab : forall X (e : E X) k,
  (* ~ inhabited X -> *)
  is_trace (Vis e k) [OutputEvent e] None
.

(* t1 ⊑ t2 *)
Definition trace_incl {E : Type -> Type} {R : Type} :
  itree E R -> itree E R -> Prop :=
  fun t1 t2 =>
    forall tr r_, is_trace t1 tr r_ -> is_trace t2 tr r_.

From ITree Require Import
     StdEffects
     OpenSum.

(* Lemma trace_incl_or : forall {E R} `{nondetE -< E} (t1 t2 : itree E R), *)
(*   trace_incl t1 (or t1 t2). *)
(* Proof. *)
(*   red. intros. unfold or. unfold vis. induction tr. *)
(*   - inversion H0; subst; try constructor. *)
(*     admit. admit. *)
(*   - destruct a. *)
(*     + apply TraceVis. *)

(* remember tr. remember t1. remember r_. unfold vis. *)
(*   induction H0; intros; subst. *)
(*   - constructor. *)
(*   - constructor. *)
(* Qed. *)

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
  (* todo well-formedness of trace *)
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
