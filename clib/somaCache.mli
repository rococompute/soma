(** Content receipts outside the checkout, bound to the active toolchain.
    Tracked files and symbolic links are never trusted. *)
val trusted : string -> bool
val record : string -> unit

(** Full toolchain identity supplied by the driver, or SHA-256 of the worker. *)
val identity : unit -> string

(** For non-object metadata, verify the exact already-read bytes against a
    producer receipt. This cannot certify .vo/.stamp files independently. *)
val trusted_metadata : string -> contents:string -> bool
