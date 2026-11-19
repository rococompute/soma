(** The same home/XDG resolution used by Envars and rc loading. *)
val home : warn:(string -> unit) -> string
val xdg_config_home : (string -> unit) -> string

(** Ordered versioned/unversioned XDG then home rc candidates. *)
val rc_candidates : warn:(string -> unit) -> string list
