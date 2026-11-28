(** Declarative, typed project build graphs. No command strings or source text. *)
type kind = Source_types | Modules | Values | Bindings | Aliases | Initializers
type part = Artifact of { extract : string; kind : kind; namespace : string }
          | Unit of string
          | Whitespace of string
type action = Extract of { file : string; source_root : string; options : string list;
                           bindings : string option; verify : bool }
            | Publish of { extract : string; file : string; output : string }
            | Compose of { output : string; parts : part list }
            | Module_list of { output : string; units : string list }
            | Dune of { directory : string; targets : string list }
type node = { name : string; needs : string list; action : action }
type t = { directory : string; targets : string list; nodes : node list; source_only : bool }
exception Error of string
val parse : SomaToml.table -> t option
val load : string -> t
val order : t -> string list -> node list
val dependencies : node -> string list
val relative_path : string -> bool
val kind_name : kind -> string
