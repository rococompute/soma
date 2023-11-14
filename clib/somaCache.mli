(** Content receipts outside the checkout, bound to the active toolchain.
    Tracked files and symbolic links are never trusted. *)
val trusted : string -> bool
val record : string -> unit
