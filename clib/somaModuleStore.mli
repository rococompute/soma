(** Optional proof-complete ordinary Soma module donors. Receipts remain the
    producer authority; a candidate never replaces recursive import freshness. *)
val source_hash : string -> string

(** Called only after the compiler has certified its own object/stamp pair.
    Only root-project .soma units are currently eligible. No .vos donor. *)
val record : root:string -> cache:string -> prefix:string -> source:string ->
  vo:string -> stamp:string -> expected:string -> unit

(** Publish producer-certified candidates after a successful build. *)
val publish : store:string -> context:string -> root:string -> cache:string -> unit

(** Atomically install candidates only if the local cache remains absent.
    Unsupported no-replace rename platforms simply retain ordinary compilation. *)
val restore : store:string -> context:string -> root:string -> cache:string -> unit

(** Atomic no-replace directory publication, also used by whole-project restore. *)
val rename_absent : string -> string -> bool

(** Remove a caller-owned private staging tree after an unsuccessful rename. *)
val remove_staging : string -> unit
