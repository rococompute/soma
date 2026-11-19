(** The implicit folder-rule selection policy, shared with import freshness.
    Fingerprints encode membership/selection, never unrelated source bodies. *)
type status = Self | Suppressed | Selected | Orphan | Absent
type candidate = { path : string; base : string; status : status; legacy : bool * bool }
val select : root:string -> root_name:string -> source:string -> candidate list option
val fingerprint : candidate list option -> string

val fallback_root_name : string -> string

(** Read the root-rule name using the same pure TOML grammar as the compiler. *)
val configured_root_name : string -> string
(** Known source-family and exact folder-rule candidates, including absent
    companions and suppressors. Does not enumerate arbitrary resources. *)
val candidate_paths : root:string -> root_name:string -> source:string -> string list
