(** Small-step semantics over the actual [Native.program] syntax.

    This layer covers synchronous control, loops, references, vectors, text
    buffers, word/string-key tables and unary callbacks. It is not semantics
    for every Native constructor: other table-key domains, higher-order string mapping, multiargument callbacks,
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
From Soma Require NativeWord NativeTable.
From Corelib Require Import PrimInt63.
From Stdlib Require Import List Arith.Wf_nat Arith.PeanoNat Strings.String Strings.Ascii ZArith Lia.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope string_scope.

Inductive fault :=
| Fault_invalid_argument (message : string)
| Fault_failure (message : string)
| Fault_assertion (file : string) (line column : nat).

Inductive cell : Type :=
| Reference_cell (A : Type) (id : nat) (value : A)
| Callback_cell (A B : Type) (id : nat) (body : A -> Native.program B)
| Array_cell (A : Type) (id : nat) (items : list A)
| Text_cell (id : nat) (contents : string)
| Fault_cell (id : nat) (description : fault)
| Table_cell (K V : Type) (domain : NativeTable.key_domain K) (id : nat) (entries : list (K * V)).
Arguments Reference_cell {A} id value.
Arguments Callback_cell {A B} id body.
Arguments Array_cell {A} id items.
Arguments Table_cell {K V} domain id entries.

Definition cell_id c := match c with
  | Reference_cell id _ | Callback_cell id _ | Array_cell id _
  | Text_cell id _ | Fault_cell id _ | Table_cell _ id _ => id
  end.
Inductive backend := Native_code | Bytecode.
Record world := Runtime_world { execution_backend : backend; next_id : nat; cells : list cell }.
Definition World next cs := Runtime_world Native_code next cs.
Definition empty_world := World 0 [].
Definition empty_world_for mode := Runtime_world mode 0 [].
Definition allocate w c := Runtime_world (execution_backend w) (S (next_id w)) (c :: cells w).
Definition replace_cells w cs := Runtime_world (execution_backend w) (next_id w) cs.
(** Exception ids zero and one denote the pre-existing Not_found and array-
    bounds singletons. New exceptions use ids above those atoms. Vector id zero
    independently denotes the canonical empty array; nonempty vector handles
    likewise use successor ids. These are typed abstract handles, not addresses. *)
Definition bounds_exception := ExceptionValue 1.
Definition fault_handle w := ExceptionValue (S (S (next_id w))).
Definition with_fault w description := allocate w (Fault_cell (next_id w) description).
(** Native bounds checks use the registered exception; bytecode's safe-array
    primitive constructs Invalid_argument on each failure. Keep that observable
    identity/allocation difference rather than collapsing the two backends. *)
Definition bounds_world w := match execution_backend w with
  | Native_code => w
  | Bytecode => with_fault w (Fault_invalid_argument "index out of bounds")
  end.
Definition bounds_value w := match execution_backend w with
  | Native_code => bounds_exception
  | Bytecode => fault_handle w
  end.
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

Inductive array_contents {A} (id : nat) (items : list A) : list cell -> Prop :=
| Array_here rest : array_contents id items (Array_cell id items :: rest)
| Array_later before rest : cell_id before <> id -> array_contents id items rest ->
    array_contents id items (before :: rest).
Inductive array_updates {A} (id : nat) (items : list A) : list cell -> list cell -> Prop :=
| Array_updates_here (old : list A) rest : List.length old = List.length items -> array_updates id items
    (Array_cell id old :: rest) (Array_cell id items :: rest)
| Array_updates_later before rest changed : cell_id before <> id -> array_updates id items rest changed ->
    array_updates id items (before :: rest) (before :: changed).

Inductive text_contents (id : nat) (text : string) : list cell -> Prop :=
| Text_here rest : text_contents id text (Text_cell id text :: rest)
| Text_later before rest : cell_id before <> id -> text_contents id text rest ->
    text_contents id text (before :: rest).
Inductive text_updates (id : nat) (text : string) : list cell -> list cell -> Prop :=
| Text_updates_here old rest : text_updates id text (Text_cell id old :: rest) (Text_cell id text :: rest)
| Text_updates_later before rest changed : cell_id before <> id -> text_updates id text rest changed ->
    text_updates id text (before :: rest) (before :: changed).

Inductive table_contents {K V} (id : nat) (domain : NativeTable.key_domain K)
    (entries : list (K * V)) : list cell -> Prop :=
| Table_here rest : table_contents id domain entries (Table_cell domain id entries :: rest)
| Table_later before rest : cell_id before <> id -> table_contents id domain entries rest ->
    table_contents id domain entries (before :: rest).

Inductive table_updates {K V} (id : nat) (domain : NativeTable.key_domain K)
    (entries : list (K * V)) : list cell -> list cell -> Prop :=
| Table_updates_here (old : list (K * V)) rest : table_updates id domain entries
    (Table_cell domain id old :: rest) (Table_cell domain id entries :: rest)
| Table_updates_later before rest changed : cell_id before <> id -> table_updates id domain entries rest changed ->
    table_updates id domain entries (before :: rest) (before :: changed).

Fixpoint replace_nth {A} (index : nat) (value : A) (items : list A) : list A :=
  match index, items with
  | 0, _ :: tail => value :: tail
  | S index, head :: tail => head :: replace_nth index value tail
  | _, [] => []
  end.

Definition text_fits text := (Z.of_nat (String.length text) <= NativeWord.string_limit)%Z.

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
    step w (Native.Call_callback (Native.Named_callback namespace name) argument) w' (@Native.Throw B error)
| Step_raise_invalid_argument A w message :
    step w (@Native.Raise_invalid_argument A message)
      (with_fault w (Fault_invalid_argument message)) (Native.Throw (fault_handle w))
| Step_raise_failure A w message :
    step w (@Native.Raise_failure A message)
      (with_fault w (Fault_failure message)) (Native.Throw (fault_handle w))
| Step_assert_failure A w file line column :
    step w (@Native.Assert_failure A file line column)
      (with_fault w (Fault_assertion file line column)) (Native.Throw (fault_handle w))
| Step_raise_not_found A w :
    step w (@Native.Raise_not_found A) w (Native.Throw (ExceptionValue 0))
| Step_vector_of_list_empty A w :
    step w (@Native.Vector_of_list A []) w (Native.Return (Native.Vector 0 0))
| Step_vector_of_list A w head (tail : list A) :
    (Z.of_nat (List.length (head :: tail)) <= NativeWord.array_limit)%Z ->
    step w (Native.Vector_of_list (head :: tail))
      (allocate w (Array_cell (next_id w) (head :: tail)))
      (Native.Return (Native.Vector (S (next_id w)) (List.length (head :: tail))))
| Step_vector_of_list_too_long A w (items : list A) :
    (NativeWord.array_limit < Z.of_nat (List.length items))%Z ->
    step w (Native.Vector_of_list items)
      (with_fault w (Fault_invalid_argument "Array.make")) (Native.Throw (fault_handle w))
| Step_vector_to_list_empty A w :
    step w (Native.Vector_to_list (@Native.Vector A 0 0)) w (Native.Return [])
| Step_vector_to_list A w id (items : list A) :
    array_contents id items (cells w) ->
    step w (Native.Vector_to_list (@Native.Vector A (S id) (List.length items))) w (Native.Return items)
| Step_vector_length_empty A w :
    step w (Native.Vector_length (@Native.Vector A 0 0)) w (Native.Return (NativeWord.of_nat 0))
| Step_vector_length A w id (items : list A) :
    array_contents id items (cells w) ->
    step w (Native.Vector_length (@Native.Vector A (S id) (List.length items)))
      w (Native.Return (NativeWord.of_nat (List.length items)))
| Step_vector_get_empty A w index :
    step w (Native.Vector_get (@Native.Vector A 0 0) index)
      (bounds_world w) (Native.Throw (bounds_value w))
| Step_vector_get A w id (items : list A) index position value :
    array_contents id items (cells w) -> NativeWord.bounded_index index (List.length items) = Some position ->
    nth_error items position = Some value ->
    step w (Native.Vector_get (@Native.Vector A (S id) (List.length items)) index) w (Native.Return value)
| Step_vector_get_invalid A w id (items : list A) index :
    array_contents id items (cells w) -> NativeWord.bounded_index index (List.length items) = None ->
    step w (Native.Vector_get (@Native.Vector A (S id) (List.length items)) index)
      (bounds_world w) (Native.Throw (bounds_value w))
| Step_vector_set_empty A w index (value : A) :
    step w (Native.Vector_set (@Native.Vector A 0 0) index value)
      (bounds_world w) (Native.Throw (bounds_value w))
| Step_vector_set A w id (items : list A) index position value changed :
    array_contents id items (cells w) -> NativeWord.bounded_index index (List.length items) = Some position ->
    array_updates id (replace_nth position value items) (cells w) changed ->
    step w (Native.Vector_set (@Native.Vector A (S id) (List.length items)) index value)
      (replace_cells w changed) (Native.Return tt)
| Step_vector_set_invalid A w id (items : list A) index value :
    array_contents id items (cells w) -> NativeWord.bounded_index index (List.length items) = None ->
    step w (Native.Vector_set (@Native.Vector A (S id) (List.length items)) index value)
      (bounds_world w) (Native.Throw (bounds_value w))
| Step_new_text_buffer w capacity :
    step w (Native.New_text_buffer capacity) (allocate w (Text_cell (next_id w) EmptyString))
      (Native.Return (Native.Text_buffer (next_id w)))
| Step_text_buffer_append w id before suffix changed :
    text_contents id before (cells w) -> text_fits (String.append before suffix) ->
    text_updates id (String.append before suffix) (cells w) changed ->
    step w (Native.Text_buffer_append (Native.Text_buffer id) suffix)
      (replace_cells w changed) (Native.Return tt)
| Step_text_buffer_append_too_long w id before suffix :
    text_contents id before (cells w) -> ~ text_fits (String.append before suffix) ->
    step w (Native.Text_buffer_append (Native.Text_buffer id) suffix)
      (with_fault w (Fault_failure "Buffer.add: cannot grow buffer")) (Native.Throw (fault_handle w))
| Step_text_buffer_char w id before character changed :
    text_contents id before (cells w) -> text_fits (String.append before (String character EmptyString)) ->
    text_updates id (String.append before (String character EmptyString)) (cells w) changed ->
    step w (Native.Text_buffer_char (Native.Text_buffer id) character)
      (replace_cells w changed) (Native.Return tt)
| Step_text_buffer_char_too_long w id before character :
    text_contents id before (cells w) -> ~ text_fits (String.append before (String character EmptyString)) ->
    step w (Native.Text_buffer_char (Native.Text_buffer id) character)
      (with_fault w (Fault_failure "Buffer.add: cannot grow buffer")) (Native.Throw (fault_handle w))
| Step_text_buffer_contents w id text :
    text_contents id text (cells w) ->
    step w (Native.Text_buffer_contents (Native.Text_buffer id)) w (Native.Return text)
| Step_string_length w text :
    text_fits text ->
    step w (Native.String_length text) w (Native.Return (NativeWord.of_nat (String.length text)))
| Step_string_get w text index position character :
    text_fits text -> NativeWord.bounded_index index (String.length text) = Some position ->
    String.get position text = Some character ->
    step w (Native.String_get text index) w (Native.Return character)
| Step_string_get_invalid w text index :
    text_fits text -> NativeWord.bounded_index index (String.length text) = None ->
    step w (Native.String_get text index) (bounds_world w) (Native.Throw (bounds_value w))
| Step_string_get_nat w text index character :
    text_fits text -> NativeWord.nat_fits index -> String.get index text = Some character ->
    step w (Native.String_get_nat text index) w (Native.Return character)
| Step_string_get_nat_invalid w text index :
    text_fits text -> NativeWord.nat_fits index -> String.get index text = None ->
    step w (Native.String_get_nat text index) (bounds_world w) (Native.Throw (bounds_value w))
| Step_string_substring w text offset count start size :
    text_fits text -> NativeWord.bounded_slice offset count (String.length text) = Some (start, size) ->
    step w (Native.String_substring text offset count) w (Native.Return (String.substring start size text))
| Step_string_substring_invalid w text offset count :
    text_fits text -> NativeWord.bounded_slice offset count (String.length text) = None ->
    step w (Native.String_substring text offset count)
      (with_fault w (Fault_invalid_argument "String.sub / Bytes.sub")) (Native.Throw (fault_handle w))
(** Capacity is a signed native word. Like Hashtbl.create, a negative hint
    still creates an empty table. Bucket layout, random seeds, native allocation
    cost/failure and mutable native string aliases are refinement obligations. *)
| Step_new_table K V w capacity (domain : NativeTable.key_domain K) :
    step w (@Native.New_table K V capacity)
      (allocate w (Table_cell (V:=V) domain (next_id w) []))
      (Native.Return (Native.Table (next_id w)))
| Step_table_mem K V w id (domain : NativeTable.key_domain K) entries key :
    table_contents (V:=V) id domain entries (cells w) ->
    step w (Native.Table_mem (@Native.Table K V id) key) w
      (Native.Return (match NativeTable.lookup domain key entries with Some _ => true | None => false end))
| Step_table_find K V w id (domain : NativeTable.key_domain K) entries key :
    table_contents (V:=V) id domain entries (cells w) ->
    step w (Native.Table_find (@Native.Table K V id) key) w
      (match NativeTable.lookup domain key entries with
       | Some value => Native.Return value | None => Native.Throw (ExceptionValue 0) end)
| Step_table_find_opt K V w id (domain : NativeTable.key_domain K) entries key :
    table_contents (V:=V) id domain entries (cells w) ->
    step w (Native.Table_find_opt (@Native.Table K V id) key) w
      (Native.Return (NativeTable.lookup domain key entries))
| Step_table_replace K V w changed id (domain : NativeTable.key_domain K) entries key value :
    table_contents (V:=V) id domain entries (cells w) ->
    table_updates id domain (NativeTable.replace domain key value entries) (cells w) changed ->
    step w (Native.Table_replace (@Native.Table K V id) key value) (replace_cells w changed) (Native.Return tt)
| Step_table_remove K V w changed id (domain : NativeTable.key_domain K) entries key :
    table_contents (V:=V) id domain entries (cells w) ->
    table_updates id domain (NativeTable.remove domain key entries) (cells w) changed ->
    step w (Native.Table_remove (@Native.Table K V id) key) (replace_cells w changed) (Native.Return tt).

Inductive steps {A} : world -> Native.program A -> world -> Native.program A -> Prop :=
| Steps_refl w body : steps w body w body
| Steps_cons w body middle following final last :
    step w body middle following -> steps middle following final last ->
    steps w body final last.

CoInductive diverges {A} : world -> Native.program A -> Prop :=
| Diverges_step w body w' body' : step w body w' body' -> diverges w' body' -> diverges w body.

(** This typed view exposes creation's supported key domain without injecting
    existential type indices or assuming a type-equality decision procedure. *)
Definition supported_table_creation {A} (body : Native.program A) :=
  match body with
  | @Native.New_table K V _ => inhabited (NativeTable.key_domain K)
  | _ => True
  end.

Theorem step_requires_supported_table_keys A w (body : Native.program A) final following :
  step w body final following -> supported_table_creation body.
Proof. intro Move. destruct Move; cbn [supported_table_creation]; eauto. Qed.

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
    (Runtime_world (execution_backend w) (S (next_id w)) (Reference_cell (next_id w) written :: cells w))
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
    (Runtime_world (execution_backend w) (S (S (next_id w)))
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

Theorem empty_vectors_share_handle A w :
  steps w (Native.Bind (@Native.Vector_of_list A []) (fun first =>
    Native.Bind (@Native.Vector_of_list A []) (fun second => Native.Return (first,second))))
    w (Native.Return (@Native.Vector A 0 0, @Native.Vector A 0 0)).
Proof.
  eapply Steps_cons; [apply Step_bind; apply Step_vector_of_list_empty|].
  eapply Steps_cons; [apply Step_bind_return|].
  eapply Steps_cons; [apply Step_bind; apply Step_vector_of_list_empty|].
  eapply Steps_cons; [apply Step_bind_return|apply Steps_refl].
Qed.

Theorem vector_replace_roundtrip A w (first second replacement : A) :
  steps w (Native.Bind (Native.Vector_of_list [first;second]) (fun vector =>
    Native.Bind (Native.Vector_set vector 1%uint63 replacement) (fun _ => Native.Vector_to_list vector)))
    (Runtime_world (execution_backend w) (S (next_id w)) (Array_cell (next_id w) [first;replacement] :: cells w))
    (Native.Return [first;replacement]).
Proof.
  eapply Steps_cons.
  - apply Step_bind, Step_vector_of_list. vm_compute. discriminate.
  - eapply Steps_cons; [apply Step_bind_return|].
    eapply Steps_cons.
    + apply Step_bind. eapply Step_vector_set with (items:=[first;second]) (position:=1)
        (changed:=Array_cell (next_id w) [first;replacement] :: cells w).
      * constructor.
      * vm_compute. reflexivity.
      * constructor. reflexivity.
    + eapply Steps_cons; [apply Step_bind_return|].
      eapply Steps_cons; [eapply Step_vector_to_list with (items:=[first;replacement]); constructor|apply Steps_refl].
Qed.

Theorem buffer_append_roundtrip w id before suffix :
  text_fits (String.append before suffix) ->
  steps (Runtime_world (execution_backend w) (next_id w) (Text_cell id before :: cells w))
    (Native.Bind (Native.Text_buffer_append (Native.Text_buffer id) suffix)
      (fun _ => Native.Text_buffer_contents (Native.Text_buffer id)))
    (Runtime_world (execution_backend w) (next_id w) (Text_cell id (String.append before suffix) :: cells w))
    (Native.Return (String.append before suffix)).
Proof.
  intro Hfits. eapply Steps_cons.
  - apply Step_bind. eapply Step_text_buffer_append; [constructor|exact Hfits|constructor].
  - eapply Steps_cons; [apply Step_bind_return|].
    eapply Steps_cons; [apply Step_text_buffer_contents; constructor|apply Steps_refl].
Qed.
End Execution.

Theorem distinct_allocated_faults w description : fault_handle w <> fault_handle (with_fault w description).
Proof. unfold fault_handle, with_fault, allocate; cbn. intro H. inversion H. lia. Qed.

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

Theorem native_bounds_preserve_world w :
  execution_backend w = Native_code -> bounds_world w = w /\ bounds_value w = bounds_exception.
Proof. intro H. unfold bounds_world, bounds_value. now rewrite H. Qed.

Theorem bytecode_bounds_allocate_fault w :
  execution_backend w = Bytecode ->
  bounds_world w = with_fault w (Fault_invalid_argument "index out of bounds") /\ bounds_value w = fault_handle w.
Proof. intro H. unfold bounds_world, bounds_value. now rewrite H. Qed.

Lemma bounds_preserve_well_formed w : well_formed w -> well_formed (bounds_world w).
Proof.
  intro H. unfold bounds_world. destruct (execution_backend w); [exact H|].
  apply allocation_preserves_well_formed; [exact H|reflexivity].
Qed.

Lemma same_identities_preserve_well_formed w changed :
  map cell_id (cells w) = map cell_id changed ->
  well_formed w -> well_formed (replace_cells w changed).
Proof.
  intros Hids [Hunique Hbound]. unfold well_formed, replace_cells; cbn.
  split; [now rewrite <- Hids|].
  change (Forall (fun c => cell_id c < next_id w) changed).
  rewrite <- (Forall_map cell_id (fun id => id < next_id w)).
  rewrite <- Hids. now rewrite Forall_map.
Qed.

Theorem array_updates_read_back A id (items : list A) before after :
  array_updates id items before after -> array_contents id items after.
Proof. intro H. induction H; constructor; assumption. Qed.

Theorem text_updates_read_back id text before after :
  text_updates id text before after -> text_contents id text after.
Proof. intro H. induction H; constructor; assumption. Qed.

Theorem array_updates_keep_identities A id (items : list A) before after :
  array_updates id items before after -> map cell_id before = map cell_id after.
Proof. intro H. induction H; cbn; congruence. Qed.

Theorem text_updates_keep_identities id text before after :
  text_updates id text before after -> map cell_id before = map cell_id after.
Proof. intro H. induction H; cbn; congruence. Qed.

Theorem array_updates_preserve_well_formed A id (items : list A) w changed :
  array_updates id items (cells w) changed -> well_formed w -> well_formed (replace_cells w changed).
Proof. intro H. apply same_identities_preserve_well_formed. now apply array_updates_keep_identities in H. Qed.

Theorem text_updates_preserve_well_formed id text w changed :
  text_updates id text (cells w) changed -> well_formed w -> well_formed (replace_cells w changed).
Proof. intro H. apply same_identities_preserve_well_formed. now apply text_updates_keep_identities in H. Qed.

Theorem table_updates_read_back K V id (domain : NativeTable.key_domain K) (entries : list (K * V)) before after :
  table_updates id domain entries before after -> table_contents id domain entries after.
Proof. intro H. induction H; constructor; assumption. Qed.

Theorem table_updates_keep_identities K V id (domain : NativeTable.key_domain K) (entries : list (K * V)) before after :
  table_updates id domain entries before after -> map cell_id before = map cell_id after.
Proof. intro H. induction H; cbn; congruence. Qed.

Theorem table_updates_preserve_well_formed K V id (domain : NativeTable.key_domain K) (entries : list (K * V)) w changed :
  table_updates id domain entries (cells w) changed -> well_formed w -> well_formed (replace_cells w changed).
Proof. intro H. apply same_identities_preserve_well_formed. now apply table_updates_keep_identities in H. Qed.

Theorem table_updates_preserve_other_reads K V A id other (domain : NativeTable.key_domain K)
    (entries : list (K * V)) (observed : A) before after :
  table_updates id domain entries before after -> reads other observed before -> reads other observed after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem table_updates_preserve_array_contents K V A id other (domain : NativeTable.key_domain K)
    (entries : list (K * V)) (items : list A) before after :
  table_updates id domain entries before after -> array_contents other items before -> array_contents other items after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem table_updates_preserve_text_contents K V id other (domain : NativeTable.key_domain K)
    (entries : list (K * V)) text before after :
  table_updates id domain entries before after -> text_contents other text before -> text_contents other text after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem table_updates_preserve_other_tables K V L W id other (domain : NativeTable.key_domain K)
    (other_domain : NativeTable.key_domain L) (entries : list (K * V)) (observed : list (L * W)) before after :
  id <> other -> table_updates id domain entries before after ->
  table_contents other other_domain observed before -> table_contents other other_domain observed after.
Proof.
  intros Different Change. induction Change; intro Read; inversion Read; subst.
  - contradiction.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem writes_preserve_table_contents A K V id other (value : A) (domain : NativeTable.key_domain K)
    (entries : list (K * V)) before after :
  writes id value before after -> table_contents other domain entries before -> table_contents other domain entries after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem array_updates_preserve_table_contents A K V id other (items : list A) (domain : NativeTable.key_domain K)
    (entries : list (K * V)) before after :
  array_updates id items before after -> table_contents other domain entries before -> table_contents other domain entries after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Theorem text_updates_preserve_table_contents K V id other text (domain : NativeTable.key_domain K)
    (entries : list (K * V)) before after :
  text_updates id text before after -> table_contents other domain entries before -> table_contents other domain entries after.
Proof.
  intros Change. induction Change; intro Read; inversion Read; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [assumption|now apply IHChange].
Qed.

Definition array_shape c :=
  (cell_id c, match c with Array_cell _ items => Some (List.length items) | _ => None end).

Theorem array_updates_preserve_shapes A id (items : list A) before after :
  array_updates id items before after -> map array_shape before = map array_shape after.
Proof.
  intro H. induction H; cbn [map array_shape cell_id].
  - change ((id,Some (List.length old)) :: map array_shape rest =
            (id,Some (List.length items)) :: map array_shape rest).
    now rewrite H.
  - now rewrite IHarray_updates.
Qed.

Theorem replace_nth_length A index (value : A) items :
  List.length (replace_nth index value items) = List.length items.
Proof. revert index. induction items; intros [|index]; cbn; auto. Qed.

Theorem replace_nth_readback A index (value old : A) items :
  nth_error items index = Some old -> nth_error (replace_nth index value items) index = Some value.
Proof.
  revert index. induction items; intros [|index] H; cbn in *; try discriminate; auto.
Qed.

Theorem replace_nth_preserves_other A index other (value : A) items :
  other <> index -> nth_error (replace_nth index value items) other = nth_error items other.
Proof.
  revert index other. induction items; intros [|index] [|other] H; cbn; try contradiction; auto.
Qed.

Theorem array_updates_preserve_other_reads A B id other (items : list A) (observed : B) before after :
  array_updates id items before after -> other <> id -> reads other observed before -> reads other observed after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst. apply Reads_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Reads_later; [assumption|now apply IHHupdate].
Qed.

Theorem text_updates_preserve_other_reads A id other text (observed : A) before after :
  text_updates id text before after -> other <> id -> reads other observed before -> reads other observed after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst. apply Reads_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Reads_later; [assumption|now apply IHHupdate].
Qed.

Theorem writes_preserve_array_contents A B id other (value : A) (items : list B) before after :
  writes id value before after -> other <> id -> array_contents other items before -> array_contents other items after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst. apply Array_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Array_later; [assumption|now apply IHHupdate].
Qed.

Theorem writes_preserve_text_contents A id other (value : A) text before after :
  writes id value before after -> other <> id -> text_contents other text before -> text_contents other text after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst. apply Text_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Text_later; [assumption|now apply IHHupdate].
Qed.

Theorem array_updates_preserve_other_arrays A B id other (items : list A) (observed : list B) before after :
  array_updates id items before after -> other <> id ->
  array_contents other observed before -> array_contents other observed after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst; [contradiction|]. apply Array_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Array_later; [assumption|now apply IHHupdate].
Qed.

Theorem text_updates_preserve_other_text id other text observed before after :
  text_updates id text before after -> other <> id ->
  text_contents other observed before -> text_contents other observed after.
Proof.
  intros Hupdate Hneq Hread. induction Hupdate.
  - inversion Hread; subst; [contradiction|]. apply Text_later; [cbn; congruence|assumption].
  - inversion Hread; subst; [constructor|]. apply Text_later; [assumption|now apply IHHupdate].
Qed.

Definition cell_bounds c := match c with
  | Array_cell _ items => 0 < List.length items /\ (Z.of_nat (List.length items) <= NativeWord.array_limit)%Z
  | Text_cell _ text => text_fits text
  | _ => True
  end.
Definition storage_bounds w := Forall cell_bounds (cells w).

Theorem writes_preserve_storage_bounds A id (value : A) w changed :
  writes id value (cells w) changed -> storage_bounds w -> storage_bounds (replace_cells w changed).
Proof.
  unfold storage_bounds, replace_cells; cbn. intro H. induction H; intro Hbounds; inversion Hbounds; subst.
  - constructor; [exact I|assumption].
  - constructor; [assumption|now apply IHwrites].
Qed.

Theorem array_updates_preserve_storage_bounds A id (items : list A) w changed :
  array_updates id items (cells w) changed -> storage_bounds w -> storage_bounds (replace_cells w changed).
Proof.
  unfold storage_bounds, replace_cells; cbn. intro H. induction H; intro Hbounds; inversion Hbounds; subst.
  - constructor; [cbn; rewrite <- H; assumption|assumption].
  - constructor; [assumption|now apply IHarray_updates].
Qed.

Theorem text_updates_preserve_storage_bounds id text w changed :
  text_updates id text (cells w) changed -> text_fits text ->
  storage_bounds w -> storage_bounds (replace_cells w changed).
Proof.
  unfold storage_bounds, replace_cells; cbn. intro H. induction H; intros Hfits Hbounds; inversion Hbounds; subst.
  - constructor; assumption.
  - constructor; [assumption|now apply IHtext_updates].
Qed.

Theorem table_updates_preserve_storage_bounds K V id (domain : NativeTable.key_domain K) (entries : list (K * V)) w changed :
  table_updates id domain entries (cells w) changed -> storage_bounds w -> storage_bounds (replace_cells w changed).
Proof.
  unfold storage_bounds, replace_cells; cbn. intro H. induction H; intro Hbounds; inversion Hbounds; subst.
  - constructor; [exact I|assumption].
  - constructor; [assumption|now apply IHtable_updates].
Qed.

Lemma allocate_preserves_storage_bounds w c :
  cell_bounds c -> storage_bounds w -> storage_bounds (allocate w c).
Proof. unfold storage_bounds, allocate; cbn. intros. now constructor. Qed.

Lemma bounds_preserve_storage_bounds w : storage_bounds w -> storage_bounds (bounds_world w).
Proof.
  intro H. unfold bounds_world. destruct (execution_backend w); [exact H|].
  apply allocate_preserves_storage_bounds; [exact I|exact H].
Qed.

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
    eauto using allocation_preserves_well_formed, writes_preserve_well_formed,
      array_updates_preserve_well_formed, text_updates_preserve_well_formed,
      table_updates_preserve_well_formed, bounds_preserve_well_formed.
Qed.

Theorem steps_preserve_well_formed A w (body : Native.program A) w' body' :
  steps foreign named w body w' body' -> well_formed w -> well_formed w'.
Proof.
  intro Hsteps. induction Hsteps; intro Hwf; eauto using step_preserves_well_formed.
Qed.
End Preservation.

Section BoundsPreservation.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.
Hypothesis foreign_preserves : forall A (primitive : unit -> A) w answer w',
  storage_bounds w -> foreign primitive w answer w' -> storage_bounds w'.
Hypothesis named_preserves : forall A B namespace name (argument : A) w (answer : result B) w',
  storage_bounds w -> named namespace name argument w answer w' -> storage_bounds w'.

Theorem step_preserves_storage_bounds A w (body : Native.program A) w' body' :
  step foreign named w body w' body' -> storage_bounds w -> storage_bounds w'.
Proof.
  intro Hstep. induction Hstep; intro Hbounds; try assumption;
    eauto using writes_preserve_storage_bounds, array_updates_preserve_storage_bounds,
      text_updates_preserve_storage_bounds, table_updates_preserve_storage_bounds,
      allocate_preserves_storage_bounds, bounds_preserve_storage_bounds.
  all: apply allocate_preserves_storage_bounds; [|assumption].
  all: cbn [cell_bounds]; auto.
  all: try (split; [apply Nat.lt_0_succ|assumption]).
  all: unfold text_fits, NativeWord.string_limit; cbn; discriminate.
Qed.

Theorem steps_preserve_storage_bounds A w (body : Native.program A) w' body' :
  steps foreign named w body w' body' -> storage_bounds w -> storage_bounds w'.
Proof. intro Hsteps. induction Hsteps; intro Hbounds; eauto using step_preserves_storage_bounds. Qed.
End BoundsPreservation.

Section BackendPreservation.
Variable foreign : forall A : Type, (unit -> A) -> world -> result A -> world -> Prop.
Variable named : forall A B : Type, string -> string -> A -> world -> result B -> world -> Prop.
Hypothesis foreign_preserves : forall A (primitive : unit -> A) w answer w',
  foreign primitive w answer w' -> execution_backend w' = execution_backend w.
Hypothesis named_preserves : forall A B namespace name (argument : A) w (answer : result B) w',
  named namespace name argument w answer w' -> execution_backend w' = execution_backend w.

Theorem step_preserves_backend A w (body : Native.program A) w' body' :
  step foreign named w body w' body' -> execution_backend w' = execution_backend w.
Proof.
  intro H. induction H; try reflexivity; eauto.
  all: unfold bounds_world; destruct (execution_backend w) eqn:E; cbn [with_fault allocate]; auto.
Qed.

Theorem steps_preserve_backend A w (body : Native.program A) w' body' :
  steps foreign named w body w' body' -> execution_backend w' = execution_backend w.
Proof.
  intro H. induction H; [reflexivity|].
  rewrite IHsteps. now apply step_preserves_backend in H.
Qed.
End BackendPreservation.
