(** * Sandbox's handles that OCaml modules name too, [Soma.Handles]

    Here rather than in Sandbox.v so that a definition (Soma.OCaml) can
    name them without making its program an image: a program is one when
    it requires Soma.Sandbox (toplevel/somaMirage.ml, [requires_mirage]).
    Sandbox exports this module. *)

(** a mutable buffer of bytes, of the length [new_buffer] gave it: what a
    program reads and writes in place, a sector, a frame, a page, rather
    than making a string of each. The image knows it as OCaml's [bytes],
    which its collector frees once nothing has it; a buffer is made only
    by [new_buffer] ([Buffer n] is no buffer). *)
Inductive buffer : Type := Buffer (id : nat).
Register buffer as soma.buffer.type.

(** what an OCaml module's function gives that ends later, an [A] once it
    has (OCaml's ['a Lwt.t] in the image): [await_promise] waits for it.
    Made only by OCaml; an OCaml module declares a function that gives
    one ([start : string -> promise nat]). *)
Inductive promise (A : Type) : Type := Promise (id : nat).
Register promise as soma.promise.type.
Arguments Promise {A} id.
