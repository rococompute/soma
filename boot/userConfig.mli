(** The same home/XDG resolution used by Envars and rc loading. *)
val home : warn:(string -> unit) -> string
val xdg_config_home : (string -> unit) -> string

(** Ordered versioned/unversioned XDG then home rc candidates. *)
val rc_candidates : warn:(string -> unit) -> string list

(** Resolve fallback environment entries beside this selected executable,
    rather than beside the caller (e.g. a driver inspecting its worker). *)
val rc_candidates_for_executable : string -> warn:(string -> unit) -> string list
