(** The implicit folder-rule selection policy, shared with import freshness.
    Fingerprints encode membership/selection, never unrelated source bodies. *)
type status = Self | Suppressed | Selected | Orphan | Absent
type candidate = { path : string; base : string; status : status; legacy : bool * bool }
val select : root:string -> root_name:string -> source:string -> candidate list option
val fingerprint : candidate list option -> string

val fallback_root_name : string -> string
