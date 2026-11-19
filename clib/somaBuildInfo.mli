(** Private compiler-to-CLI build metadata. Paths and argv are NUL-delimited,
    never shell command fragments. External inputs are fingerprinted before
    product generation and rechecked by the CLI before certifying freshness. *)
type input = string * string
val signature : ?write:bool -> string -> string
val prepare_inputs : string list -> input list option
val mark_external : unit -> unit
val publish_inputs : input list option -> unit
val publish_products : string list -> unit
val publish_command : string list -> unit
