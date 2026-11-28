(** Compositional total-correctness rules for Native's actual control syntax.
    Typed elimination views avoid injecting existential type indices or using
    proof irrelevance when inspecting indexed program constructors. *)
From Soma Require Import Native NativeSemantics NativeTotal.
From Stdlib Require Import Strings.String.
Set Implicit Arguments.

Section Control.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.

Definition control_successor {A} w (body : Native.program A) w' (following : Native.program A) :=
  (match body in Native.program T return Native.program T -> Prop with
  | @Native.Bind X Y before next => fun last =>
      (exists before', step foreign named w before w' before' /\ last = Native.Bind before' next) \/
      (exists value, before = Native.Return value /\ w' = w /\ last = next value) \/
      (exists error, before = Native.Throw error /\ w' = w /\ last = Native.Throw error)
  | @Native.Invoke X Y primitive next => fun last =>
      (exists value, foreign primitive w (Returned value) w' /\ last = next value) \/
      (exists error, foreign primitive w (Raised error) w' /\ last = Native.Throw error)
  | @Native.Loop state_type value_type body initial => fun last =>
      w' = w /\ last = Native.Bind (body initial) (fun progress => match progress with
        | Native.Continue state => Native.Loop body state
        | Native.Finish value => Native.Return value end)
  | _ => fun _ => True
  end) following.

Theorem step_control_successor A w (body : Native.program A) w' following :
  step foreign named w body w' following -> control_successor w body w' following.
Proof. intro Move. destruct Move; cbn [control_successor]; eauto 8. Qed.

Theorem total_bind A B (before_post : world -> result A -> Prop)
    (post : world -> result B -> Prop) (current : configuration (A:=A))
    (next : A -> Native.program B) :
  total foreign named before_post current ->
  (forall w' value, before_post w' (Returned value) -> total foreign named post (w', next value)) ->
  (forall w' error, before_post w' (Raised error) -> post w' (Raised error)) ->
  total foreign named post (fst current, Native.Bind (snd current) next).
Proof.
  intros [Accessible Safe] Continue Recover. revert Safe.
  induction Accessible as [[w before] All IH]. intro Safe.
  apply successors_give_total.
  - destruct (Safe (w, before) (Steps_refl foreign named w before))
      as [[answer [Equal BeforePost]]|[[w' following] Move]].
    + cbn in Equal, BeforePost. subst before. destruct answer.
      * exists (w, next value). unfold transition; cbn. apply Step_bind_return.
      * exists (w, Native.Throw error). unfold transition; cbn. apply Step_bind_throw.
    + exists (w', Native.Bind following next). unfold transition in *; cbn in *.
      now apply Step_bind.
  - intros [w' following] Move. unfold transition in Move; cbn in Move.
    apply step_control_successor in Move. cbn [control_successor] in Move.
    destruct Move as [[before' [Move Equal]]|[[value [Equal [World Following]]]|[error [Equal [World Following]]]]].
    + subst following. apply (IH (w', before') Move).
      eapply safe_after_step; [exact Safe|exact Move].
    + subst before w' following. apply Continue.
      apply (@total_outcome_requires_postcondition foreign named A before_post w (Returned value)).
      split; [constructor; exact All|exact Safe].
    + subst before w' following. apply throw_is_total, Recover.
      apply (@total_outcome_requires_postcondition foreign named A before_post w (Raised error)).
      split; [constructor; exact All|exact Safe].
Qed.

Theorem total_bind_return A B post w (value : A) (next : A -> Native.program B) :
  total foreign named post (w, next value) ->
  total foreign named post (w, Native.Bind (Native.Return value) next).
Proof.
  intro Continue.
  eapply (total_bind (before_post := fun final answer => final = w /\ answer = Returned value)
    (current := (w, Native.Return value))).
  - apply return_is_total. auto.
  - intros final observed [World Equal]. inversion Equal; subst. exact Continue.
  - intros final error [_ Equal]. discriminate.
Qed.

Theorem total_invoke A B post w (primitive : unit -> A) (next : A -> Native.program B) :
  (exists answer final, foreign primitive w answer final) ->
  (forall final value, foreign primitive w (Returned value) final ->
    total foreign named post (final, next value)) ->
  (forall final error, foreign primitive w (Raised error) final -> post final (Raised error)) ->
  total foreign named post (w, Native.Invoke primitive next).
Proof.
  intros [answer [final Call]] Continue Recover. apply successors_give_total.
  - destruct answer.
    + exists (final, next value). unfold transition; cbn. now apply Step_invoke.
    + exists (final, Native.Throw error). unfold transition; cbn. now apply Step_invoke_raise.
  - intros [final' following] Move. unfold transition in Move; cbn in Move.
    apply step_control_successor in Move. cbn [control_successor] in Move.
    destruct Move as [[value [Call' Equal]]|[error [Call' Equal]]]; subst following.
    + now apply Continue.
    + apply throw_is_total. now apply Recover.
Qed.

Definition loop_resume {S A} (body : S -> Native.program (Native.progress S A)) progress :=
  match progress with
  | Native.Continue state => Native.Loop body state
  | Native.Finish value => Native.Return value
  end.

Theorem total_loop_unroll S A post w (body : S -> Native.program (Native.progress S A)) initial :
  total foreign named post (w, Native.Bind (body initial) (loop_resume body)) ->
  total foreign named post (w, Native.Loop body initial).
Proof.
  intro Unrolled. apply successors_give_total.
  - exists (w, Native.Bind (body initial) (loop_resume body)).
    unfold transition, loop_resume; cbn. apply Step_loop.
  - intros [final following] Move. unfold transition in Move; cbn in Move.
    apply step_control_successor in Move. cbn [control_successor] in Move.
    destruct Move as [World Equal]. subst final following. exact Unrolled.
Qed.

Theorem total_loop_step S A post w (body : S -> Native.program (Native.progress S A)) initial :
  total foreign named (fun final answer => match answer with
    | Returned progress => total foreign named post (final, loop_resume body progress)
    | Raised error => post final (Raised error)
    end) (w, body initial) ->
  total foreign named post (w, Native.Loop body initial).
Proof.
  intro Iteration. apply total_loop_unroll.
  eapply (total_bind (current := (w, body initial))); [exact Iteration| |];
    intros; assumption.
Qed.

Theorem total_loop_continue S A post w (body : S -> Native.program (Native.progress S A)) initial next :
  body initial = Native.Return (Native.Continue next) ->
  total foreign named post (w, Native.Loop body next) ->
  total foreign named post (w, Native.Loop body initial).
Proof.
  intros Body Continue. apply total_loop_unroll. rewrite Body.
  now apply total_bind_return.
Qed.

Theorem total_loop_finish S A post w (body : S -> Native.program (Native.progress S A)) initial value :
  body initial = Native.Return (Native.Finish value) -> post w (Returned value) ->
  total foreign named post (w, Native.Loop body initial).
Proof.
  intros Body Post. apply total_loop_unroll. rewrite Body.
  apply total_bind_return, return_is_total. exact Post.
Qed.
End Control.
