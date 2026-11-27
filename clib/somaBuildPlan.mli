(** Declarative, typed project build graphs. No command strings or source text. *)
type kind = Source_types | Modules | Values | Bindings | Aliases | Initializers
type part = Artifact of { extract : string; kind : kind; namespace : string }
          | Unit of string
type action = Extract of { file : string; source_root : string; options : string list;
                           bindings : string option }
            | Compose of { output : string; parts : part list }
            | Dune of { directory : string; targets : string list }
type node = { name : string; needs : string list; action : action }
type t = { directory : string; targets : string list; nodes : node list }
exception Error of string
val parse : SomaToml.table -> t option
val load : string -> t
val order : t -> string list -> node list
val dependencies : node -> string list
val relative_path : string -> bool
val kind_name : kind -> string
