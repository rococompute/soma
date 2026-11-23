(** * Effects at an extracted library boundary

    [program A] describes synchronous execution and native promise scopes.
    Building a program does not execute it in Soma. [entry A] marks a boundary
    at which generated native code executes the program and returns an [A].
    There is deliberately no evaluator [program A -> A] in the logic.

    These are library computations, not Mirage device actions: requiring this
    module does not make a program a Sandbox image. Native primitive callbacks
    remain explicit trusted interfaces. *)
Require Export Soma.Handles.
From Stdlib Require Import Strings.String.

(** The native result representation, for callbacks supplied by existing
    libraries. Constructors and payloads retain their native identities. *)
Inductive result (A E : Type) := Ok (value : A) | Error (error : E).
Arguments Ok {A E} value.
Arguments Error {A E} error.
Register result as soma.native.result.

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
Arguments Export {A} body.

Register program as soma.native.program.
Register entry as soma.native.entry.

(** A value-preserving native barrier, for scopes that intentionally keep a
    borrowed resource alive through an observable callback. *)
Definition opaque {A} (value : A) := value.

(** Preserve an ordinary caller frame around a native entry invocation.
    This remains an identity on symbolic entries, not an evaluator. *)
Definition ordinary {A} (value : entry A) : entry A := value.
