(** * Effects at an extracted library boundary

    [program A] describes synchronous execution and native promise scopes.
    Building a program does not execute it in Soma. [entry A] marks a boundary
    at which generated native code executes the program and returns an [A].
    There is deliberately no evaluator [program A -> A] in the logic.

    These are library computations, not Mirage device actions: requiring this
    module does not make a program a Sandbox image. Native primitive callbacks
    remain explicit trusted interfaces. *)
Require Export Soma.Handles.
Require Import Soma.Word64.
From Stdlib Require Import Strings.String Strings.Ascii.
From Corelib Require Import PrimInt63.

(** An owned native function, callable only through an effect. Its logical
    handle contains no evaluator and is independent of the program syntax's
    universe. The runtime creates it with [New_callback], preserving physical
    identity even when its body refers to itself. *)
Inductive callback (A B : Type) : Type := Callback (id : nat)
 | Named_callback (namespace name : string).
Arguments Callback {A B} id.
Arguments Named_callback {A B} namespace name.
Register callback as soma.native.callback.

(** Compiler-declared native types have a canonical name in the logical type.
    Constructors are placeholders, never a way to construct or inspect the
    external value. Generated typed bindings are the only runtime boundary. *)
Inductive native_handle (name : string) : Type := Native_handle (id : nat).
Arguments Native_handle {name} id.
Register native_handle as soma.native.handle.
(** Parameterized native schemas preserve their logical type arguments.
    Distinct instantiations cannot be interchanged through a phantom alias. *)
Inductive native_family (name:string)(arguments:Type):Type := Native_family(id:nat).
Arguments Native_family {name arguments} id.
Register native_family as soma.native.family.


(** Native owned storage. Sizes and indices use the existing machine-word
    type, preserving negative values and native bounds errors at the ABI. This
    reuses [PrimInt63.int], the existing kernel primitive type; no storage
    axiom or logical evaluator is introduced. *)
(** The logical size is readonly, as is a native array's header. Elements
    remain native mutable storage; no logical array evaluator is introduced. *)
Inductive vector (A : Type) : Type := Vector (id size : nat).
Inductive text_buffer : Type := Text_buffer (id : nat).
Inductive table (K V : Type) : Type := Table (id : nat).
Arguments Vector {A} id size. Arguments Table {K V} id.
Register vector as soma.native.vector.
Register text_buffer as soma.native.text_buffer.
Register table as soma.native.table.

(** The native result representation, for callbacks supplied by existing
    libraries. Constructors and payloads retain their native identities. *)
Inductive result (A E : Type) := Ok (value : A) | Error (error : E).
Arguments Ok {A E} value.
Arguments Error {A E} error.
Register result as soma.native.result.

(** A native flat triple. Coq's chained binary products have a different
    runtime layout, so native three-component APIs use this explicit shape. *)
Inductive triple (A B C : Type) := Triple (first : A) (second : B) (third : C).
Arguments Triple {A B C} first second third.
Register triple as soma.native.triple.

Inductive quadruple (A B C D:Type) := Quadruple (first:A)(second:B)(third:C)(fourth:D).
Arguments Quadruple {A B C D} first second third fourth.
Register quadruple as soma.native.quadruple.

Inductive quintuple (A B C D E : Type) :=
| Quintuple (first : A) (second : B) (third : C) (fourth : D) (fifth : E).
Arguments Quintuple {A B C D E} first second third fourth fifth.
Register quintuple as soma.native.quintuple.


Inductive progress (S A : Type) := Continue (state : S) | Finish (value : A).
Arguments Continue {S A} state.
Arguments Finish {S A} value.

Inductive program : Type -> Type :=
| Return {A} (value : A) : program A
| Invoke {A B} (primitive : unit -> A) (next : A -> program B) : program B
| Bind {A B} (before : program A) (next : A -> program B) : program B
| Loop {S A} (step : S -> program (progress S A)) (initial : S) : program A
| Protect {A} (body : program A) (recover : exception_value -> program A) : program A
| Throw {A} (error : exception_value) : program A
| Promise_return {A} (value : A) : program (promise A)
| Promise_map {A B} (body : unit -> promise A) (next : A -> entry B) : program (promise B)
| Promise_bind {A B} (body : unit -> promise A) (next : A -> entry (promise B)) : program (promise B)
| Promise_catch {A} (body : unit -> entry (promise A))
    (recover : exception_value -> entry (promise A)) : program (promise A)
| Promise_finally {A} (body : unit -> entry (promise A))
    (cleanup : unit -> entry (promise unit)) : program (promise A)
| Promise_fold {A B} (step : A -> B -> entry (promise A)) (initial : A) (items : list B) : program (promise A)
| Promise_map_s {A B} (step : A -> entry (promise B)) (items : list A) : program (promise (list B))
| Promise_fail {A} (error : exception_value) : program (promise A)
| New_reference {A} (value : A) : program (reference A)
| Read_reference {A} (location : reference A) : program A
| Write_reference {A} (location : reference A) (value : A) : program unit
| Assert_failure {A} (file : string) (line column : nat) : program A
| Filter {A} (predicate : A -> bool) (items : list A) : program (list A)
| New_callback {A B} (body : callback A B -> A -> program B) : program (callback A B)
| Call_callback {A B} (body : callback A B) (argument : A) : program B
| Vector_of_list {A} (items : list A) : program (vector A)
| Vector_to_list {A} (items : vector A) : program (list A)
| Vector_length {A} (items : vector A) : program PrimInt63.int
| Vector_get {A} (items : vector A) (index : PrimInt63.int) : program A
| Vector_set {A} (items : vector A) (index : PrimInt63.int) (value : A) : program unit
| New_text_buffer (capacity : PrimInt63.int) : program text_buffer
| Text_buffer_append (buffer : text_buffer) (text : string) : program unit
| Text_buffer_char (buffer : text_buffer) (character : ascii) : program unit
| Text_buffer_contents (buffer : text_buffer) : program string
| New_table {K V} (capacity : PrimInt63.int) : program (table K V)
| Table_mem {K V} (entries : table K V) (key : K) : program bool
| Table_find {K V} (entries : table K V) (key : K) : program V
| Table_find_opt {K V} (entries : table K V) (key : K) : program (option V)
| Table_replace {K V} (entries : table K V) (key : K) (value : V) : program unit
| Table_remove {K V} (entries : table K V) (key : K) : program unit
| String_map (mapper : callback ascii ascii) (text : string) : program string
| String_get (text : string) (index : PrimInt63.int) : program ascii
| String_get_nat (text : string) (index : nat) : program ascii
| Word_decimal (value : PrimInt63.int) : program string
| Nat_decimal (value : nat) : program string
| Path_basename (path : string) : program string
| Path_dirname (path : string) : program string
| Path_concat (directory file : string) : program string
| Promise_apply {A} (body : unit -> entry (promise A)) : program (promise A)
| Promise_map_entry {A B} (body : unit -> entry (promise A)) (next : A -> entry B) : program (promise B)
| Promise_bind_entry {A B} (body : unit -> entry (promise A)) (next : A -> entry (promise B)) : program (promise B)
| New_deferred {A} (body : unit -> entry (promise A)) : program (deferred A)
| Force_deferred {A} (body : deferred A) : program (promise A)
| String_substring (text : string) (offset count : PrimInt63.int) : program string
| Raise_not_found {A} : program A
| String_length (text : string) : program PrimInt63.int
| Vector_map {A B} (mapper : callback A B) (items : vector A) : program (vector B)
| Promise_both {A B} (left : promise A) (right : promise B) : program (promise (A * B))
| Raise_failure {A} (message : string) : program A
(** Multiargument callbacks create one native curried closure. Nested
    [New_callback] allocations instead execute between partial applications. *)
| New_callback2 {A B R}
    (body : callback A (callback B R) -> A -> B -> program R)
    : program (callback A (callback B R))
| New_callback6 {A B C D E F R}
    (body : callback A (callback B (callback C (callback D (callback E (callback F R))))) ->
      A -> B -> C -> D -> E -> F -> program R)
    : program (callback A (callback B (callback C (callback D (callback E (callback F R))))))
| Promise_unit : program (promise unit)
| Promise_none {A} : program (promise (option A))
| Promise_settled {A} (pending : promise A) : program bool
| Promise_pick {A} (pending : list (promise A)) : program (promise A)
| Int64_of_int (value : PrimInt63.int) : program Word64.word64
| Raise_invalid_argument {A} (message : string) : program A
(** Keep the caller's consumed owner in the native call frame until the
    provider returns. Native liveness may discard the dead owner earlier;
    bytecode preserves its argument slot, as for a direct bind expression. *)
| Promise_bind_borrowed {Owner A B} (owner : Owner) (body : unit -> promise A)
    (next : A -> entry (promise B)) : program (promise B)
| List_map {A B}(mapper:callback A B)(items:list A) : program(list B)
| Promise_map_borrowed {Owner A B}(owner:Owner)(body:unit->promise A)
 (next:A->entry B) : program(promise B)
| New_callback3 {A B C R}
 (body : (callback A (callback B (callback C (R)))) -> A -> B -> C -> program R)
 : program (callback A (callback B (callback C (R))))
| New_callback4 {A B C D R}
 (body : (callback A (callback B (callback C (callback D (R))))) -> A -> B -> C -> D -> program R)
 : program (callback A (callback B (callback C (callback D (R)))))
| New_callback5 {A B C D E R}
 (body : (callback A (callback B (callback C (callback D (callback E (R)))))) -> A -> B -> C -> D -> E -> program R)
 : program (callback A (callback B (callback C (callback D (callback E (R))))))
| Call_callback2 {A B R} (body : callback A (callback B (R)))
 (a0:A) (a1:B) : program R
| Call_callback3 {A B C R} (body : callback A (callback B (callback C (R))))
 (a0:A) (a1:B) (a2:C) : program R
| Call_callback4 {A B C D R} (body : callback A (callback B (callback C (callback D (R)))))
 (a0:A) (a1:B) (a2:C) (a3:D) : program R
| Call_callback5 {A B C D E R} (body : callback A (callback B (callback C (callback D (callback E (R))))))
 (a0:A) (a1:B) (a2:C) (a3:D) (a4:E) : program R
| Call_callback6 {A B C D E F R} (body : callback A (callback B (callback C (callback D (callback E (callback F (R)))))))
 (a0:A) (a1:B) (a2:C) (a3:D) (a4:E) (a5:F) : program R
(** Pure functions need no per-call entry program. The handle remains opaque;
    this creates no logical native callback evaluator. *)
| Pure_callback {A B} (body:A->B) : program(callback A B)
| Pure_callback2 {A B R} (body:A->B->R) : program(callback A(callback B R))
(** A consumed incoming argument remains in a direct synchronous caller's
    bytecode frame through [before], then leaves before the tail continuation.
    The native backend can release the unused argument sooner. *)
| Borrowed_scope {Owner A B} (owner:Owner) (before:program A)
 (next:A->program B) : program B
with entry : Type -> Type :=
| Export {A} (body : program A) : entry A.

Arguments Return {A} value.
Arguments Invoke {A B} primitive next.
Arguments Bind {A B} before next.
Arguments Loop {S A} step initial.
Arguments Protect {A} body recover.
Arguments Throw {A} error.
Arguments Promise_return {A} value.
Arguments Promise_map {A B} body next.
Arguments Promise_bind {A B} body next.
Arguments Promise_catch {A} body recover.
Arguments Promise_finally {A} body cleanup.
Arguments Promise_fold {A B} step initial items.
Arguments Promise_map_s {A B} step items.
Arguments Promise_fail {A} error.
Arguments New_reference {A} value.
Arguments Read_reference {A} location.
Arguments Write_reference {A} location value.
Arguments Assert_failure {A} file line column.
Arguments Filter {A} predicate items.
Arguments New_callback {A B} body.
Arguments New_callback2 {A B R} body.
Arguments Promise_none {A}.
Arguments Promise_settled {A} pending.
Arguments Promise_pick {A} pending.
Arguments New_callback6 {A B C D E F R} body.
Arguments Call_callback {A B} body argument.
Arguments Vector_of_list {A} items.
Arguments Vector_to_list {A} items.
Arguments Vector_length {A} items.
Arguments Vector_get {A} items index.
Arguments Vector_set {A} items index value.
Arguments New_table {K V} capacity.
Arguments Table_mem {K V} entries key.
Arguments Table_find {K V} entries key.
Arguments Table_find_opt {K V} entries key.
Arguments Table_replace {K V} entries key value.
Arguments Table_remove {K V} entries key.
Arguments Promise_apply {A} body.
Arguments Promise_map_entry {A B} body next.
Arguments Promise_bind_entry {A B} body next.
Arguments New_deferred {A} body.
Arguments Force_deferred {A} body.
Arguments Raise_not_found {A}.
Arguments Vector_map {A B} mapper items.
Arguments Promise_both {A B} left right.
Arguments Raise_failure {A} message.
Arguments Raise_invalid_argument {A} message.
Arguments Promise_bind_borrowed {Owner A B} owner body next.
Arguments List_map {A B} mapper items.
Arguments Promise_map_borrowed {Owner A B} owner body next.
Arguments Export {A} body.

Register program as soma.native.program.
Register entry as soma.native.entry.

(** A separate boundary for mutually recursive callbacks. Extending this
    boundary leaves [program]'s representation and existing proof receipts
    unchanged. Every callback body and the final continuation remain checked
    programs; no logical evaluator is provided. *)
Local Abbreviation callback4 A B C D R :=
  (callback A (callback B (callback C (callback D R)))).
Inductive callback_group : Type -> Type :=
| Group_bind {State A} (before : program State)
    (next : State -> callback_group A) : callback_group A
| Export_callback_pair {A B C D R}
    (left : callback A B -> callback C D -> A -> program B)
    (right : callback A B -> callback C D -> C -> program D)
    (next : callback A B -> callback C D -> program R) : callback_group R
| Export_callback_pair4 {A B C D R E F G H S T}
    (left : callback4 A B C D R -> callback4 E F G H S -> A -> B -> C -> D -> program R)
    (right : callback4 A B C D R -> callback4 E F G H S -> E -> F -> G -> H -> program S)
    (next : callback4 A B C D R -> callback4 E F G H S -> program T) : callback_group T.
Arguments Group_bind {State A} before next.
Arguments Export_callback_pair {A B C D R} left right next.
Arguments Export_callback_pair4 {A B C D R E F G H S T} left right next.
Register callback_group as soma.native.callback_group.


(** Create an ordinary nonrecursive callback with the lexical captures of
    its body. The symbolic program uses a callback that ignores itself. *)
Definition lexical_callback3 {A B C R}
    (body : A -> B -> C -> program R) : program (callback A (callback B (callback C (R)))) :=
  New_callback3 (fun _ a b c => body a b c).
Register lexical_callback3 as soma.native.lexical_callback3.

Definition lexical_callback5 {A B C D E R}
    (body : A -> B -> C -> D -> E -> program R) : program (callback A (callback B (callback C (callback D (callback E (R)))))) :=
  New_callback5 (fun _ a b c d e => body a b c d e).
Register lexical_callback5 as soma.native.lexical_callback5.

Definition lexical_callback6 {A B C D E F R}
    (body : A -> B -> C -> D -> E -> F -> program R) : program (callback A (callback B (callback C (callback D (callback E (callback F (R))))))) :=
  New_callback6 (fun _ a b c d e f => body a b c d e f).
Register lexical_callback6 as soma.native.lexical_callback6.

(** A value-preserving native barrier, for scopes that intentionally keep a
    borrowed resource alive through an observable callback. *)
Definition opaque {A} (value : A) := value.

(** Preserve an ordinary caller frame around a native entry invocation.
    This remains an identity on symbolic entries, not an evaluator. *)
Definition ordinary {A} (value : entry A) : entry A := value.

(** Fuse a consuming loop with its terminal continuation. The native loop
    tailcalls [next] after finishing, without a separate caller frame that
    retains the initial input while the loop consumes it. There is no logical
    evaluator: the symbolic computation is ordinary [Bind] after [Loop]. *)
Definition loop_then {S A B} (step : S -> program (progress S A)) (initial : S)
    (next : A -> program B) : program B := Bind (Loop step initial) next.

(** Run an unbounded state machine whose step and terminal observation are
    ordinary functions. Native lowering avoids constructing a progress tag
    and effect thunk for every transition. The logical program remains an
    ordinary [Loop] with a returned progress value. *)
Definition loop_values {S A} (step : S -> S) (finish : S -> option A)
    (initial : S) : program A :=
  Loop (fun state => Return (match finish state with
    | Some value => Finish value
    | None => Continue (step state)
    end)) initial.

(** Continue after a consuming value loop without keeping its initial state
    in an outer bind frame. Like [loop_then], this is a symbolic [Bind]. *)
Definition loop_values_then {S A B} (step : S -> S) (finish : S -> option A)
    (initial : S) (next : A -> program B) : program B :=
  Bind (loop_values step finish initial) next.

(** Final primitive calls must tailcall their provider. An [Invoke] followed
    by [Return] has the same symbolic result but retains an extra caller frame
    around the primitive on bytecode. This fused native boundary drops it. *)
Definition tail_invoke {A} (primitive:unit->A) : program A := Invoke primitive Return.

(** The native string's byte count as a primitive machine word. The logical
    definition takes its low 63 bits; native OCaml strings fit in that range. *)
Definition word_length (text:string) : PrimInt63.int :=
 Soma.Word64.Int63Bits.of_N (BinNat.N.of_nat (String.length text)).

(** Pure readonly observations preserve native caller expression shapes. The
    ghost size describes the array header, which element updates preserve. *)
Definition vector_size {A}(items:vector A) : nat :=
 match items with Vector _ size=>size end.
Definition vector_word_size {A}(items:vector A) : PrimInt63.int :=
 Soma.Word64.Int63Bits.of_N(BinNat.N.of_nat(vector_size items)).

Arguments New_callback3 {A B C R} body.
Arguments New_callback4 {A B C D R} body.
Arguments New_callback5 {A B C D E R} body.
Arguments Call_callback2 {A B R} body a0 a1.
Arguments Call_callback3 {A B C R} body a0 a1 a2.
Arguments Call_callback4 {A B C D R} body a0 a1 a2 a3.
Arguments Call_callback5 {A B C D E R} body a0 a1 a2 a3 a4.
Arguments Call_callback6 {A B C D E F R} body a0 a1 a2 a3 a4 a5.

Arguments Pure_callback {A B} body.
Arguments Pure_callback2 {A B R} body.

Arguments Borrowed_scope {Owner A B} owner before next.

(** A native callback followed immediately by its continuation needs no
    intermediate callback program or tuple of nested programs. *)
Definition call_then {A B R}(body:callback A B)(argument:A)
 (next:B->program R) : program R := Bind(Call_callback body argument)next.
