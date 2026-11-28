(** Small-step semantics over the actual [Native.program] syntax.

    This first layer covers synchronous control, loops, references and unary
    callbacks. It is deliberately not a claim of semantics for every Native
    constructor: vectors, tables, buffers, strings, multiargument callbacks,
    promises/deferred scheduling and physical GC still need their rules.
    In particular an unsupported operation is stuck, never silently pure.

    Foreign invocation/named callbacks have explicit state/result relations.
    They may mutate the heap or raise before returning. No evaluator, axiom,
    arbitrary interpreter for owned operations or universal progress premise
    is installed. Refinement proofs must discharge the relevant foreign laws.
    Heap lookup/update are typed relations, with no [Any], casts, type-equality
    oracle or erased-value store. Allocation uses abstract fresh identities;
    it does not model native/bytecode physical allocation costs or GC. *)
From Soma Require Import Native.
From Stdlib Require Import List Arith.Wf_nat Arith.PeanoNat Strings.String.
Import ListNotations.
Set Implicit Arguments.

Inductive cell : Type :=
| Reference_cell (A : Type) (id : nat) (value : A)
| Callback_cell (A B : Type) (id : nat) (body : A -> Native.program B).
Arguments Reference_cell {A} id value.
Arguments Callback_cell {A B} id body.

Definition cell_id c := match c with
  | Reference_cell id _ | Callback_cell id _ => id
  end.
Record world := World { next_id : nat; cells : list cell }.
Definition empty_world := World 0 [].
Definition allocate w c := World (S (next_id w)) (c :: cells w).
Definition replace_cells w cs := World (next_id w) cs.
Definition well_formed w :=
  NoDup (map cell_id (cells w)) /\
  Forall (fun c => cell_id c < next_id w) (cells w).

Inductive reads {A} (id : nat) (value : A) : list cell -> Prop :=
| Reads_here rest : reads id value (Reference_cell id value :: rest)
| Reads_later before rest : cell_id before <> id -> reads id value rest ->
    reads id value (before :: rest).

Inductive writes {A} (id : nat) (value : A) : list cell -> list cell -> Prop :=
| Writes_here (old : A) rest : writes id value
    (Reference_cell id old :: rest) (Reference_cell id value :: rest)
| Writes_later before rest changed : cell_id before <> id -> writes id value rest changed ->
    writes id value (before :: rest) (before :: changed).

Inductive callback_body {A B} (id : nat) (body : A -> Native.program B) : list cell -> Prop :=
| Callback_here rest : callback_body id body (Callback_cell id body :: rest)
| Callback_later before rest : cell_id before <> id -> callback_body id body rest ->
    callback_body id body (before :: rest).

Inductive result (A : Type) := Returned (value : A) | Raised (error : exception_value).
Arguments Returned {A} value.
Arguments Raised {A} error.

Section Execution.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.

Inductive step : forall A : Type, world -> Native.program A -> world -> Native.program A -> Prop :=
| Step_bind A B w w' (before before' : Native.program A) (next : A -> Native.program B) :
    step w before w' before' ->
    step w (Native.Bind before next) w' (Native.Bind before' next)
| Step_bind_return A B w (value : A) (next : A -> Native.program B) :
    step w (Native.Bind (Native.Return value) next) w (next value)
| Step_bind_throw A B w error (next : A -> Native.program B) :
    step w (Native.Bind (Native.Throw error) next) w (Native.Throw error)
| Step_invoke A B w w' (primitive : unit -> A) (next : A -> Native.program B) value :
    foreign primitive w (Returned value) w' ->
    step w (Native.Invoke primitive next) w' (next value)
| Step_invoke_raise A B w w' (primitive : unit -> A) (next : A -> Native.program B) error :
    foreign primitive w (Raised error) w' ->
    step w (Native.Invoke primitive next) w' (Native.Throw error)
| Step_loop S A w (body : S -> Native.program (Native.progress S A)) initial :
    step w (Native.Loop body initial) w
      (Native.Bind (body initial) (fun progress => match progress with
        | Native.Continue state => Native.Loop body state
        | Native.Finish value => Native.Return value end))
| Step_protect A w w' (body body' : Native.program A) recover :
    step w body w' body' ->
    step w (Native.Protect body recover) w' (Native.Protect body' recover)
| Step_protect_return A w (value : A) recover :
    step w (Native.Protect (Native.Return value) recover) w (Native.Return value)
| Step_protect_throw A w error (recover : exception_value -> Native.program A) :
    step w (Native.Protect (Native.Throw error) recover) w (recover error)
| Step_new_reference A w (value : A) :
    step w (Native.New_reference value)
      (allocate w (Reference_cell (next_id w) value)) (Native.Return (Reference (next_id w)))
| Step_read_reference A w id (value : A) :
    reads id value (cells w) ->
    step w (Native.Read_reference (Reference id)) w (Native.Return value)
| Step_write_reference A w changed id (value : A) :
    writes id value (cells w) changed ->
    step w (Native.Write_reference (Reference id) value) (replace_cells w changed) (Native.Return tt)
| Step_new_callback A B w (body : Native.callback A B -> A -> Native.program B) :
    step w (Native.New_callback body)
      (allocate w (Callback_cell (next_id w) (body (Native.Callback (next_id w)))))
      (Native.Return (Native.Callback (next_id w)))
| Step_call_callback A B w id (body : A -> Native.program B) argument :
    callback_body id body (cells w) ->
    step w (Native.Call_callback (Native.Callback id) argument) w (body argument)
| Step_named_callback A B w w' namespace name (argument : A) (value : B) :
    named namespace name argument w (Returned value) w' ->
    step w (Native.Call_callback (Native.Named_callback namespace name) argument) w' (Native.Return value)
| Step_named_callback_raise A B w w' namespace name (argument : A) error :
    named (B:=B) namespace name argument w (Raised error) w' ->
    step w (Native.Call_callback (Native.Named_callback namespace name) argument) w' (@Native.Throw B error).

Inductive steps {A} : world -> Native.program A -> world -> Native.program A -> Prop :=
| Steps_refl w body : steps w body w body
| Steps_cons w body middle following final last :
    step w body middle following -> steps middle following final last ->
    steps w body final last.

CoInductive diverges {A} : world -> Native.program A -> Prop :=
| Diverges_step w body w' body' : step w body w' body' -> diverges w' body' -> diverges w body.

Definition entry_runs {A} w (code : Native.entry A) w' (answer : result A) : Prop :=
  (match code in Native.entry T return result T -> Prop with Native.Export body => fun result =>
    match result with
    | Returned value => steps w body w' (Native.Return value)
    | Raised error => steps w body w' (Native.Throw error)
    end
  end) answer.

Lemma steps_trans A w (body : Native.program A) middle following final last :
  steps w body middle following -> steps middle following final last ->
  steps w body final last.
Proof. intros H. induction H; intros; eauto using Steps_cons. Qed.

Lemma steps_bind A B w w' (body body' : Native.program A) (next : A -> Native.program B) :
  steps w body w' body' -> steps w (Native.Bind body next) w' (Native.Bind body' next).
Proof. intro H. induction H; eauto using Steps_refl, Steps_cons, Step_bind. Qed.

Lemma steps_protect A w w' (body body' : Native.program A) recover :
  steps w body w' body' -> steps w (Native.Protect body recover) w' (Native.Protect body' recover).
Proof. intro H. induction H; eauto using Steps_refl, Steps_cons, Step_protect. Qed.

Theorem invocation_raise_reaches_handler A B w w' (primitive : unit -> A)
    (next : A -> Native.program B) recover error :
  foreign primitive w (Raised error) w' ->
  steps w (Native.Protect (Native.Invoke primitive next) recover) w' (recover error).
Proof.
  intro H. eapply Steps_cons; [apply Step_protect; eapply Step_invoke_raise; exact H|].
  eapply Steps_cons; [apply Step_protect_throw|apply Steps_refl].
Qed.

Lemma loop_finishes S A w w' (body : S -> Native.program (Native.progress S A)) state value :
  steps w (body state) w' (Native.Return (Native.Finish value)) ->
  steps w (Native.Loop body state) w' (Native.Return value).
Proof.
  intro H. eapply Steps_cons; [apply Step_loop|].
  eapply steps_trans; [apply steps_bind; exact H|].
  eapply Steps_cons; [apply Step_bind_return|apply Steps_refl].
Qed.

Lemma loop_continues S A w w' (body : S -> Native.program (Native.progress S A)) state next :
  steps w (body state) w' (Native.Return (Native.Continue next)) ->
  steps w (Native.Loop body state) w' (Native.Loop body next).
Proof.
  intro H. eapply Steps_cons; [apply Step_loop|].
  eapply steps_trans; [apply steps_bind; exact H|].
  eapply Steps_cons; [apply Step_bind_return|apply Steps_refl].
Qed.

(** This rule constructs a finite successful execution from finite iteration
    witnesses and a decreasing measure. It is weak normalization: additional
    foreign transitions may permit other executions or divergence. Strong
    normalization/universal loop correctness still needs separate proof.
    There is no fuel or runtime input cap. *)
Theorem loop_has_terminating_execution S A (body : S -> Native.program (Native.progress S A))
    (invariant : S -> world -> Prop) (measure : S -> nat) :
  (forall state w, invariant state w ->
    exists w' progress, steps w (body state) w' (Native.Return progress) /\
      match progress with
      | Native.Continue next => invariant next w' /\ measure next < measure state
      | Native.Finish _ => True end) ->
  forall state w, invariant state w ->
    exists w' value, steps w (Native.Loop body state) w' (Native.Return value).
Proof.
  intros Hbody state. revert state.
  refine (well_founded_induction (well_founded_ltof S measure)
    (fun state => forall w, invariant state w ->
      exists w' value, steps w (Native.Loop body state) w' (Native.Return value)) _).
  intros state IH w Hstate.
  destruct (Hbody state w Hstate) as [w' [progress [Hrun Hprogress]]].
  destruct progress as [next|value].
  - destruct Hprogress as [Hnext Hless].
    destruct (IH next Hless w' Hnext) as [final [value Hdone]].
    exists final, value. eapply steps_trans; [eapply loop_continues; exact Hrun|exact Hdone].
  - exists w', value. now apply loop_finishes.
Qed.

Theorem spinning_loop_diverges S A w (initial : S) :
  diverges w (Native.Loop (fun state => Native.Return (@Native.Continue S A state)) initial).
Proof.
  cofix IH. eapply Diverges_step; [apply Step_loop|].
  eapply Diverges_step; [apply Step_bind_return|exact IH].
Qed.

Theorem reference_roundtrip A w (initial written : A) :
  steps w
    (Native.Bind (Native.New_reference initial) (fun location =>
      Native.Bind (Native.Write_reference location written) (fun _ =>
        Native.Read_reference location)))
    (World (S (next_id w)) (Reference_cell (next_id w) written :: cells w))
    (Native.Return written).
Proof.
  eapply Steps_cons; [apply Step_bind; apply Step_new_reference|].
  eapply Steps_cons; [apply Step_bind_return|].
  eapply Steps_cons; [apply Step_bind; apply Step_write_reference; constructor|].
  eapply Steps_cons; [apply Step_bind_return|].
  eapply Steps_cons; [apply Step_read_reference; constructor|apply Steps_refl].
Qed.

(** A callback need not return to have effects. Its write survives the raise,
    and the handler receives that exact exception object and the new value. *)
Theorem callback_write_then_raise A w (initial written : A) error :
  let location := Reference (next_id w) in
  let with_reference := allocate w (Reference_cell (next_id w) initial) in
  let body := fun (_ : Native.callback A (A * exception_value)) (value : A) =>
    Native.Bind (Native.Write_reference location value) (fun _ => @Native.Throw (A * exception_value) error) in
  steps with_reference
    (Native.Bind (Native.New_callback body) (fun callback =>
      Native.Protect (Native.Call_callback callback written) (fun caught =>
        Native.Bind (Native.Read_reference location) (fun observed => Native.Return (observed,caught)))))
    (World (S (S (next_id w)))
      (Callback_cell (S (next_id w)) (body (Native.Callback (S (next_id w)))) ::
       Reference_cell (next_id w) written :: cells w))
    (Native.Return (written,error)).
Proof.
  cbn zeta.
  eapply Steps_cons; [apply Step_bind; apply Step_new_callback|].
  eapply Steps_cons; [apply Step_bind_return|].
  eapply Steps_cons; [apply Step_protect; apply Step_call_callback; constructor|].
  eapply Steps_cons.
  - apply Step_protect, Step_bind, Step_write_reference.
    apply Writes_later; [cbn; apply Nat.neq_succ_diag_l|constructor].
  - eapply Steps_cons; [apply Step_protect; apply Step_bind_return|].
    eapply Steps_cons; [apply Step_protect_throw|].
    eapply Steps_cons.
    + apply Step_bind, Step_read_reference.
      apply Reads_later; [cbn; apply Nat.neq_succ_diag_l|constructor].
    + eapply Steps_cons; [apply Step_bind_return|apply Steps_refl].
Qed.
End Execution.

Theorem writes_read_back A id (value : A) before after :
  writes id value before after -> reads id value after.
Proof. intro H. induction H; constructor; assumption. Qed.

Theorem writes_keep_identities A id (value : A) before after :
  writes id value before after -> map cell_id before = map cell_id after.
Proof. intro H. induction H; cbn; congruence. Qed.

Theorem writes_preserve_other_reads A B id other (value : A) (observed : B) before after :
  writes id value before after -> other <> id -> reads other observed before ->
  reads other observed after.
Proof.
  intros Hwrite Hneq Hread. induction Hwrite.
  - inversion Hread; subst.
    + contradiction.
    + apply Reads_later; [cbn; congruence|assumption].
  - inversion Hread; subst.
    + constructor.
    + apply Reads_later; [assumption|now apply IHHwrite].
Qed.

Theorem writes_preserve_well_formed A id (value : A) w changed :
  writes id value (cells w) changed -> well_formed w -> well_formed (replace_cells w changed).
Proof.
  intros Hwrite [Hunique Hbound]. unfold well_formed, replace_cells; cbn.
  pose proof (writes_keep_identities Hwrite) as Hids.
  split; [now rewrite <- Hids|].
  change (Forall (fun c => cell_id c < next_id w) changed).
  rewrite <- (Forall_map cell_id (fun id => id < next_id w)).
  rewrite <- Hids. now rewrite Forall_map.
Qed.

Theorem allocation_preserves_well_formed w c :
  well_formed w -> cell_id c = next_id w -> well_formed (allocate w c).
Proof.
  intros [Hunique Hbound] Hfresh. split; cbn.
  - constructor; [|exact Hunique]. rewrite Hfresh. intro Hin.
    apply in_map_iff in Hin. destruct Hin as [old [Hid Hin]].
    rewrite Forall_forall in Hbound. specialize (Hbound old Hin). rewrite Hid in Hbound.
    exact (Nat.lt_irrefl _ Hbound).
  - constructor; [rewrite Hfresh; apply Nat.lt_succ_diag_r|].
    eapply Forall_impl; [|exact Hbound]. intros old H. now apply Nat.lt_lt_succ_r.
Qed.

Theorem empty_world_well_formed : well_formed empty_world.
Proof. split; constructor. Qed.

Section Preservation.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.
Hypothesis foreign_preserves : forall A (primitive : unit -> A) w answer w',
  well_formed w -> foreign primitive w answer w' -> well_formed w'.
Hypothesis named_preserves : forall A B namespace name (argument : A) w (answer : result B) w',
  well_formed w -> named namespace name argument w answer w' -> well_formed w'.

Theorem step_preserves_well_formed A w (body : Native.program A) w' body' :
  step foreign named w body w' body' -> well_formed w -> well_formed w'.
Proof.
  intro Hstep. induction Hstep; intro Hwf; try assumption;
    eauto using allocation_preserves_well_formed, writes_preserve_well_formed.
Qed.

Theorem steps_preserve_well_formed A w (body : Native.program A) w' body' :
  steps foreign named w body w' body' -> well_formed w -> well_formed w'.
Proof.
  intro Hsteps. induction Hsteps; intro Hwf; eauto using step_preserves_well_formed.
Qed.
End Preservation.
