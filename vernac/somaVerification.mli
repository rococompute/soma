(** Source-owned, kernel-enforced publication requirements. *)
val declare : properties:string -> invariants:string -> trusted:string -> unit
val begin_source : string -> unit
val seal : source:string -> unit
val enforce : source:string -> output:string -> interface:bool -> unit
val receipt : source:string -> string option
