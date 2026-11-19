(** A producer-certified completed checking/extraction phase. A hit still
    performs the ordinary native Dune validation and final product copy. *)
type plan = {
  key : string; source : string; root : string; directory : string;
  switch : string; output : string;
  generated : SomaBuildInfo.input list;
  imports : SomaBuildInfo.input list;
}
val requested : unit -> bool
val refuse : unit -> unit
val with_import : string -> (unit -> 'a) -> 'a
val finish_checking : imports:string list -> unit
val eligible : unit -> bool
val plugin : package:string -> files:string list -> unit
val with_project_lock : string -> (string -> 'a) -> 'a
val publish : source:string -> directory:string -> switch:string -> output:string ->
  generated:SomaBuildInfo.input list -> unit
val read : string -> plan option
val validate : plan -> bool
val record_path : string -> string option
val promote : draft:string -> key:string -> bool
val resume : plan -> run:(directory:string -> log:string -> bool) -> bool
