From ITree Require Import
     ITree.

(* Trace style, a la Compcert (but with nondeterminism) *)
(* Module Trace. *)
(*   Inductive Event : Type := *)
(*   | E1: nat -> nat -> Event. *)
(*   Inductive World : Type *)
(*     (* := W (f : nat -> option (nat * World)) *) *)
(*   . *)
(*   Inductive State : Type. *)

(*   (* Prop to handle nondeterminism *) *)
(*   (* TODO: Previously part of world defn? what is the world if we take these out? *) *)
(*   Inductive handler (e : Event) (w w' : World) : Prop. *)
(*   Fixpoint handler_det (e : Event) (w : World) : World. Admitted. *)

(*   (* handlers internal in operational semantics *) *)
(*   Inductive big (w w' : World * State) : Prop. *)
(*   Inductive small (w w' : World * State) : Prop. *)

(*   (* handlers external to operational semantics *) *)
(*   (* can use stream instead of list to model divergence *) *)
(*   Inductive big' (s : State) (s' : State * list Event) : Prop. *)
(*   Inductive small' (s : State) (s' : State * option Event) : Prop. *)

(*   (* We can use the handler + the external semantics to simulate the internal semantics *) *)
(*   Inductive big'' : (World * State) -> (World * State) -> Prop := *)
(*   | b_nil : forall w s s', big' s (s', nil) -> *)
(*                       big'' (w, s) (w, s') *)
(*   | b_cons : forall w w' w'' s s' s'' e l, big' s (s', (cons e l)) -> *)
(*                                       handler e w w' -> *)
(*                                       (* TODO: a different list of events can be used here, is that OK? *) *)
(*                                       big'' (w', s') (w'', s'') -> *)
(*                                       big'' (w, s) (w'', s''). *)

(*   Inductive small'' : (World * State) -> (World * State) -> Prop := *)
(*   | s_none : forall w s s', small' s (s', None) -> *)
(*                        small'' (w, s) (w, s') *)
(*   | s_some : forall w w' s s' e, small' s (s', Some e) -> *)
(*                             handler e w w' -> *)
(*                             small'' (w, s) (w', s'). *)

(* End Trace. *)

Module Trace'.
  (* "E O I" *)
  Inductive Event: Type -> Type -> Type :=
  | Read : forall (l : nat) (v : nat), Event nat nat
  | Write : forall (l : nat) (v : nat), Event (nat * nat) void
  .

  (* TODO: add relational version of handler here, Yannick mentioned records? *)
  Inductive World : Type
    (* := W (f : nat -> option (nat * World)) *)
  .
  Definition State := nat.

  (* Prop to handle nondeterminism *)
  Inductive handler {O I} (e : Event O I) (w w' : World) : Prop.
  Fixpoint handler_det {O I} (e : Event O I) (w : World) : World. Admitted.

  (* handlers internal in operational semantics *)
  Inductive big (w w' : World * State) : Prop.
  Inductive small (w w' : World * State) : Prop.

  (* handlers external to operational semantics *)
  (* can use stream instead of list to model divergence *)
  Inductive big' : forall O I, State -> State * list (Event O I) -> Prop := .
  Inductive small' (* {O I} *) : forall O I, State -> State * option (Event O I) -> Prop :=
  | s_none : forall s O I, small' O I s (s, None)
  | s_read : forall s l v, small' _ _ s (s, Some (Read l v))
  | s_write : forall s l v, small' _ _ s (s + v, Some (Write l v))
  .

  (* We can use the handler + the external semantics to simulate the internal semantics *)
  Inductive big'' {O I} : (World * State) -> (World * State) -> Prop :=
  | b_nil : forall w s s', big' O I s (s', nil) ->
                      big'' (w, s) (w, s')
  | b_cons : forall w w' w'' s s' s'' e l, big' O I s (s', (cons e l)) ->
                                      handler e w w' ->
                                      (* TODO: a different list of events can be used here, is that OK? *)
                                      big'' (w', s') (w'', s'') ->
                                      big'' (w, s) (w'', s'').

  Inductive small'' {O I} : (World * State) -> (World * State) -> Prop :=
  | s_none' : forall w s s', small' O I s (s', None) ->
                       small'' (w, s) (w, s')
  | s_some' : forall w w' s s' e, small' O I s (s', Some e) ->
                            handler e w w' ->
                            small'' (w, s) (w', s').

  (* Definition small''' : forall O I, State -> State * itree (Event O) I. Admitted. *)

  (* Inductive traces_itrees : (forall O I, State -> State * list (Event O I) -> Prop) -> *)
  (*                           (forall O I, State -> State * itree (Event O) I) -> *)
  (*                           Prop := *)
  (* | trace_none: forall O I s s' t e, small' O I s (s', None) -> *)
  (*                           (* recurse on s' to get some itree *) *)
  (*                           (_, t) = (small''' O I s') -> *)
  (*                           (s', Tau t). *)
  (* | f : forall s s' e, *)
  (*     small' s (s', e) -> *)

  Inductive small''' : forall O I, State -> State * itree (Event O) I -> Prop :=
  | s_none''' : forall O I s s' s'' t,
      small' O I s (s', None) ->
      small''' O I s' (s'', t) ->
      (* this should be one step, return a default value? (but how do we know there is one?) *)
      small''' O I s (s', Tau t)
  | s_some''' : forall O I s s' e,
      small' O I s (s', Some e) ->
      (* small''' O I s' (s'', t) -> *)
      small''' O I s (s', Vis e (fun b => Ret b))
  .


End Trace'.

(* CoInductive World : Type. *)

CoInductive World : Type :=
  handler (f : forall O I, E O I -> O -> I * World).

(* (* alternative definitions of world? *) *)

(* Definition handler' W := forall O I, E O I -> O -> (I * W). *)
(* Fail CoInductive world' := handler' world'. *)

(* Definition handler'' W (X : W) := forall O I, E O I -> O -> (I * W). *)
(* Definition world'' := exists W w, handler'' W w. *)
