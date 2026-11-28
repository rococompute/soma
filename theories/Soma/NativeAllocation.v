(** Total correctness of owned unary callback allocation. This uses the actual
    Native constructor and typed heap cell, without executing the stored body
    or assuming foreign progress, type equality or proof irrelevance. Physical
    allocation/GC/compiler refinement remains outside the abstract heap. *)
From Soma Require Import Native NativeSemantics NativeTotal NativeControl.
From Stdlib Require Import Strings.String.
Set Implicit Arguments.

Section Allocation.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.

Definition callback_world {A B} (w : world) (factory : Native.callback A B -> A -> Native.program B) :=
  allocate w (Callback_cell (next_id w) (factory (Native.Callback (next_id w)))).

Definition callback_successor {A} w (body : Native.program A) final (following : Native.program A) :=
  (match body in Native.program T return Native.program T -> Prop with
  | @Native.New_callback X Y factory => fun last =>
      final = callback_world w factory /\
      last = Native.Return (Native.Callback (next_id w))
  | _ => fun _ => True
  end) following.

Theorem step_callback_successor A w (body : Native.program A) final following :
  step foreign named w body final following -> callback_successor w body final following.
Proof. intro Move. destruct Move; cbn [callback_successor]; eauto. Qed.

Theorem new_callback_is_total A B post w (factory : Native.callback A B -> A -> Native.program B) :
  post (callback_world w factory)
    (Returned (Native.Callback (next_id w))) ->
  total foreign named post (w,Native.New_callback factory).
Proof.
  intro Post. apply successors_give_total.
  - exists (callback_world w factory, Native.Return (Native.Callback (next_id w))).
    unfold transition, callback_world; cbn. apply Step_new_callback.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_callback_successor in Move. cbn [callback_successor] in Move.
    destruct Move as [World Following]. subst final following. now apply return_is_total.
Qed.

Theorem new_callback_requires_postcondition A B post w
    (factory : Native.callback A B -> A -> Native.program B) :
  total foreign named post (w,Native.New_callback factory) ->
  post (callback_world w factory)
    (Returned (Native.Callback (next_id w))).
Proof.
  intro Total. apply (@total_outcome_requires_postcondition foreign named (Native.callback A B) post
    (callback_world w factory) (Returned (Native.Callback (next_id w)))).
  eapply total_preserved_by_step; [exact Total|]. unfold transition; cbn. apply Step_new_callback.
Qed.

Theorem bind_new_callback_is_total A B C post w
    (factory : Native.callback A B -> A -> Native.program B)
    (next : Native.callback A B -> Native.program C) :
  total foreign named post
    (callback_world w factory, next (Native.Callback (next_id w))) ->
  total foreign named post (w,Native.Bind (Native.New_callback factory) next).
Proof.
  intro Continue.
  eapply (total_bind (before_post:=fun final answer =>
    final = callback_world w factory /\
    answer = Returned (Native.Callback (next_id w)))
    (current:=(w,Native.New_callback factory))).
  - apply new_callback_is_total. split; reflexivity.
  - intros final value [World Equal]. inversion Equal; subst. exact Continue.
  - intros final error [_ Equal]. discriminate.
Qed.
End Allocation.
