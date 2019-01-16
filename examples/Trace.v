From ITree Require Import
     ITree.

(* Trace style, a la Compcert (but with nondeterminism) *)
Module Trace.
  Inductive Event: Type :=
  | E1: nat -> nat -> Event.
  Inductive World : Type
    (* := W (f : nat -> option (nat * World)) *)
  .
  Inductive State : Type.

  (* Prop to handle nondeterminism *)
  (* TODO: Previously part of world defn? what is the world if we take these out? *)
  Inductive handler (e : Event) (w w' : World) : Prop.
  Fixpoint handler_det (e : Event) (w : World) : World. Admitted.

  (* handlers internal in operational semantics *)
  Inductive big (w w' : World * State) : Prop.
  Inductive small (w w' : World * State) : Prop.

  (* handlers external to operational semantics *)
  (* can use stream instead of list to model divergence *)
  Inductive big' (s : State) (s' : State * list Event) : Prop.
  Inductive small' (s : State) (s' : State * option Event) : Prop.

  (* We can use the handler + the external semantics to simulate the internal semantics *)
  Inductive big'' : (World * State) -> (World * State) -> Prop :=
  | b_nil : forall w s s', big' s (s', nil) ->
                      big'' (w, s) (w, s')
  | b_cons : forall w w' w'' s s' s'' e l, big' s (s', (cons e l)) ->
                                      handler e w w' ->
                                      (* TODO: a different list of events can be used here, is that OK? *)
                                      big'' (w', s') (w'', s'') ->
                                      big'' (w, s) (w'', s'').

  Inductive small'' : (World * State) -> (World * State) -> Prop :=
  | s_none : forall w s s', small' s (s', None) ->
                       small'' (w, s) (w, s')
  | s_some : forall w w' s s' e, small' s (s', Some e) ->
                            handler e w w' ->
                            small'' (w, s) (w', s').

End Trace.

Module Trace'.
  Inductive Event (O I : Type): Type :=
  | E_1 : O -> I -> Event O I.
  Inductive World : Type
    (* := W (f : nat -> option (nat * World)) *)
  .
  Inductive State : Type.

  (* Prop to handle nondeterminism *)
  (* TODO: Previously part of world defn? what is the world if we take these out? *)
  Inductive handler {O I} (e : Event O I) (w w' : World) : Prop.
  Fixpoint handler_det {O I} (e : Event O I) (w : World) : World. Admitted.

  (* handlers internal in operational semantics *)
  Inductive big (w w' : World * State) : Prop.
  Inductive small (w w' : World * State) : Prop.

  (* handlers external to operational semantics *)
  (* can use stream instead of list to model divergence *)
  Inductive big' {O I} (s : State) (s' : State * list (Event O I)) : Prop.
  Inductive small' {O I} (s : State) (s' : State * option (Event O I)) : Prop.

  (* We can use the handler + the external semantics to simulate the internal semantics *)
  Inductive big'' {O I} : (World * State) -> (World * State) -> Prop :=
  | b_nil : forall w s s', @big' O I s (s', nil) ->
                      big'' (w, s) (w, s')
  | b_cons : forall w w' w'' s s' s'' e l, @big' O I s (s', (cons e l)) ->
                                      handler e w w' ->
                                      (* TODO: a different list of events can be used here, is that OK? *)
                                      big'' (w', s') (w'', s'') ->
                                      big'' (w, s) (w'', s'').

  Inductive small'' {O I} : (World * State) -> (World * State) -> Prop :=
  | s_none : forall w s s', @small' O I s (s', None) ->
                       small'' (w, s) (w, s')
  | s_some : forall w w' s s' e, @small' O I s (s', Some e) ->
                            handler e w w' ->
                            small'' (w, s) (w', s').

End Trace'.

(* CoInductive World : Type. *)

CoInductive World : Type :=
  handler (f : forall O I, E O I -> O -> I * World).

Inductive State : Type.

(* "internal" handlers *)
Definition big (w w' : World * State) : Prop := True.
Definition small (w w' : World * State) : Prop := True.

(* "external" handlers *)
Definition big' {O I} (s : State) (s' : State * list (E O I)) :=
  True.
Definition small' {O I} (s : State) (s' : State * option (E O I)) :=
  True.

(* (* alternative definitions of world? *) *)

(* Definition handler' W := forall O I, E O I -> O -> (I * W). *)
(* Fail CoInductive world' := handler' world'. *)

(* Definition handler'' W (X : W) := forall O I, E O I -> O -> (I * W). *)
(* Definition world'' := exists W w, handler'' W w. *)
