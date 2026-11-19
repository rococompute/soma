(** Completion provenance for content-keyed Rocq library entries. *)
type entry = { completion_digest : string; theories : (string * string) list; inputs : (string * string) list; inputs_complete : bool; artifacts : (string * string) list }
val marker : string
val load : key:string -> directory:string -> resolve_input:(string -> string) -> entry option
val source_snapshot : directory:string -> (string * string) list
val publish : key:string -> directory:string -> sources:(string * string) list -> theories:(string * string) list -> unit
val artifact_digest : entry -> directory:string -> file:string -> string option
